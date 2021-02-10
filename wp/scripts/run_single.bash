set -uo pipefail

FUNCTION=""
BINARIES=()

# Parse CLI for obtaining function name and binary paths
function parse_command_line() {
  while [ $# -gt 0 ]; do
    case "$1" in
      --function)
        FUNCTION="$2"
        shift
        shift
        ;;
      -* | --*)
        echo "Invalid flag: $1"
        exit 0
        ;;
      *)
        BINARIES+=("$1")
        shift
        ;;
    esac
  done
}

# Checks if user inputted a function
function check_function() {
  if [ -z "$FUNCTION" ]; then
    echo 'WP needs a function to compare.'
    exit 1
  fi
}

# Checks if the user inputted two binaries to compare.
function check_binaries() {
  if [ "${#BINARIES[@]}" -ne 2 ]; then
    echo 'WP needs two binaries to compare.'
    exit 1
  fi
}

# Run on a single function
function run() {
  echo $FUNCTION | parallel \
    "bap wp \
    --no-byteweight \
    --function={} \
    --num-unroll=0 \
    --show=paths,bir \
    --compare-post-reg-values=R12,R13,R14,R15,RBX,RSP,RBP,RAX \
    --rewrite-addresses \
    --check-invalid-derefs \
    ${BINARIES[0]} ${BINARIES[1]}"
}

parse_command_line $@
check_function
check_binaries

time run
