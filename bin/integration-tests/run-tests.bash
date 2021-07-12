# -------------------------
#
# Run the integration tests
#
# -------------------------

# Define useful paths
THIS_SCRIPT="${BASH_SOURCE[0]}"
THIS_DIR="$(cd "$(dirname "${THIS_SCRIPT}")" && pwd)"
COMMON_LIB_DIR="$(cd "${THIS_DIR}/../common-lib" && pwd)"

# Include needed libraries
. "${COMMON_LIB_DIR}/utils.bash"
. "${COMMON_LIB_DIR}/slack.bash"

# Report progress to slack?
REPORT_PROGRESS="false"

usage () {
    echo "USAGE: bash  [OPTIONS]"
    echo ""
    echo "  Run the integration tests."
    echo ""
    echo "OPTIONS"
    echo "  -h | --help       Print this help and exit" 
    echo "  --report-results  Report the results to slack"
}


#-----what does "#" do?
# # number of args
# todo: simple script using
# arith mode: (()) 
while ((${#})); do 
    case "${1}" in
	
	 -h|--help)
	 usage
	 exit 1
	 ;;
	
	 --report-results)
	 REPORT_RESULTS="true"
	 ;;
	
	 *)
	   echo "Unrecognized input ${1}"
	   help_hint
	   exit 1
	   ;;
    esac
    shift #remove front one and move up one, and then renumbering
done

#Todo: exit 1
#Todo: Try running ls -la /tmp


# Call `clean up` before the script ends
# When OS throws signal, one is exit.
# When throws exits, catch it, then call cleanup,
# Then rethrow exit 
trap clean_up EXIT 

# Ensures we have a slack URL to post with
if [[ "${REPORT_RESULTS}"=="true" ]]; then
    there_is_a_SLACK_USERNAME
    # single [ is "test"
    # todo: google "test" for command line
    if [ ${?} -ne 0 ];then
	echo "Halting."
	echo "Need a SLACK_USERNAME environment variable."
	echo "Export one to proceed."
	exit 1
    fi
    there_is_a_SLACK_URL
    # maybe the same as (( ${?} = 0 ))
    if [ ${?} -ne 0 ]; then
	echo "Halting."
	echo "Need a SLACK_URL environment variable."
	echo "Export one to proceed."
	exit 1
    fi
fi

# Where to record progress
REPORT="$(report_file "${REPORT_RESULTS}")" #------report_file

# Record some useful info
bap_version
git_commit

echo ""

# Prep for the test runs.
#------REPO_ROOT
#------tee?
make clean "${REPO_ROOT}"/cbat_tools 2>&1 | tee "${REPORT_FILE}"

# Todo: test global/context stuff with vars ??? 

# Run the integration tests.
make test.integration -C "${REPO_ROOT}" 2>&1 | tee -a "${REPORT_FILE}"
TEST_RESULT="${?}"
echo "REPORT:"
cat "${REPORT_FILE}" 
if [[ "${TEST_RESULT}" != "0" ]]; then
    echo "Integration tests failed" > "${MSG_FILE}"
    if [[ "${REPORT_RESULTS}" == "true" ]]; then
	report_to_slack
    fi
    fail
    exit 1
else
    echo "Integration tests passed" > "${MSG_FILE}"
    if [[ "${REPORT_RESULTS}" == "true" ]]; then
	report_to_slack
    fi
fi
