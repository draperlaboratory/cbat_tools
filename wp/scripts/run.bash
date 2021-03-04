set -uo pipefail

# Default output location
OUTPUT=$(pwd)/output.$(date '+%m-%d-%Y-%H-%M-%S')

# Default number of jobs to run in parallel
JOBS=1

# Default timeout in seconds
TIMEOUT=1000

BINARIES=()

# Prints out the help/usage message.
function print_help() {
  printf '%s\n' "-- WP batch running script --"
  printf '%s\n' "This runs WP to compare all subroutines between two binaries."
  printf '%s\n' "Compares all subs with the default settings that compare post"
  printf '%s\n' "callee-saved register values."
  printf '\t%s\n' "1. Does not unroll loops."
  printf '\t%s\n' "2. Rewrites addresses of global variables in the modified"
  printf '\t%-3s%s\n' " " "binary to their addresses in the original binary."
  printf '\t%s\n' "3. If the address of a memory read is at a valid location in"
  printf '\t%-3s%s\n' " " "the original binary, checks if that same address is"
  printf '\t%-3s%s\n' " " "at a valid location in the modified binary."
  printf '\nUsage:\n%s ' "$(basename $0)"
  printf '%s\n' "[-j|--jobs] [-t|--timeout] [-o|--output] -- <original> <modified>"
  printf '\t%s\n' "- jobs: How many jobs to run in parallel (default: 1)"
  printf '\t%s\n' "- timeout: Timeout for each job (default: 1000s)"
  printf '\t%s\n' "- output: Location of logs and results of each subroutine"
  printf '\t%-10s%s\n' " " "(default: output-<date>)"
}

# Parse CLI for overriding default options.
function parse_command_line() {
  while [ $# -gt 0 ]; do
    case "$1" in
      -j | --jobs)
        JOBS="$2"
        shift
        shift
        ;;
      -t | --timeout)
        TIMEOUT="$2"
        shift
        shift
        ;;
      -o | --output)
        OUTPUT="$2"
        shift
        shift
        ;;
      -h | --help)
        print_help
        exit 0
        ;;
      -* | --*)
        echo "Invalid flag: $1"
        print_help
        exit 0
        ;;
      *)
        BINARIES+=("$1")
        shift
        ;;
    esac
  done
}

# Check that parallel is installed.
function check_parallel() {
  if ! command -v parallel --version > /dev/null 2>&1; then
    echo "'parallel' is not installed"
    exit 1
  fi
}

# Checks if the user inputted two binaries to compare.
function check_binaries() {
  if [ "${#BINARIES[@]}" -ne 2 ]; then
    echo 'WP needs two binaries to compare.'
    print_help
    exit 1
  fi
}

# Generate a list of all subroutines in the original binary
# (except those of the form sub_* and %abcd1234).
function get_all_subs() {
  bap -dsymbols --no-byteweight ${BINARIES[0]} \
    | sed -r 's/\s*$//g; /^sub_[0-9a-f]+$/d; /^\%[0-9a-f]+$/d;' \
    > $NAMES
}

# Looks at the results from the previous run and creates a list of subroutines
# that resulted in SAT or UNKNOWN.
function get_sats_and_unknowns() {
  grep -L '^UNSAT!$' $RESULTS/* | xargs -L 1 basename
}

# Run WP on the first subroutine of the binaries to prime the cache. Note there
# is no timeout on this run.
function prime_cache() {
  head -n 1 $NAMES \
    | parallel --eta --joblog $LOGS/prime.txt -j $JOBS \
    "bap wp \
    --no-byteweight \
    --function={} \
    --num-unroll=0 \
    ${BINARIES[0]} ${BINARIES[1]} > /dev/null 2>&1"
}

# Run WP on all subroutines with the default settings.
function run() {
  cat $NAMES \
    | parallel --eta --joblog $LOGS/invalid-derefs.txt --timeout $TIMEOUT -j $JOBS \
    "bap wp \
    --no-byteweight \
    --function={} \
    --num-unroll=0 \
    --show=bir,paths \
    --compare-post-reg-values=R12,R13,R14,R15,RBX,RSP,RBP,RAX \
    --rewrite-addresses \
    --check-invalid-derefs \
    ${BINARIES[0]} ${BINARIES[1]} > $RESULTS/{} 2>&1"
}

# Prints out the number of each result from the run.
function show_results() {
  sats=$(grep -l '^SAT!$' $RESULTS/* | wc -l)
  unsats=$(grep -l '^UNSAT!$' $RESULTS/* | wc -l)
  unknowns=$(grep -L '^SAT!$\|^UNSAT!$' $RESULTS/* | wc -l)
  total=$(ls $RESULTS/ | wc -l)
  echo "----------------"
  echo "SATs: $sats"
  echo "UNSATs: $unsats"
  echo "UNKNOWNs: $unknowns"
  echo "TOTAL: $total"
  echo "----------------"
}

# --------------------------------------------------------------

# The main program

parse_command_line $@
check_parallel
check_binaries

NAMES=$OUTPUT/names.txt
LOGS=$OUTPUT/logs
RESULTS=$OUTPUT/results
STATS=$OUTPUT/stats.txt

mkdir -p $OUTPUT $LOGS $RESULTS

echo "Comparing '${BINARIES[0]}' and '${BINARIES[1]}'." | tee -a $STATS

echo "Generating list of all subroutines in original."
get_all_subs

echo "Priming caches."
prime_cache

START=$SECONDS

run
show_results | tee -a $STATS

END=$SECONDS

echo "Elapsed time: $(date -u -d @$(($END - $START)) +'%T')" | tee -a $STATS
