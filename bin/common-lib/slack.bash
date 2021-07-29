# -------------------------------
#
# Utilities for slack integration
#
# -------------------------------

# DESC: Checks if SLACK_USERNAME is defined
# OUTPUT: 0 if SLACK_USERNAME is defined, 1 otherwise
there_is_a_SLACK_USERNAME () {
    if [ -z "${SLACK_USERNAME}" ];
    then return 1;
    else return 0;
    fi
}

# DESC: Checks if SLACK_URL is defined
# OUTPUT: 0 if SLACK_URL is defined, 1 otherwise
there_is_a_SLACK_URL () {
    if [ -z "${SLACK_URL}" ];
    then return 1;
    else return 0;
    fi
}

# DESC: Creates a payload JSON file.
# OUTPUT: The exit code of the attempt to write the file.
build_slack_payload () {
    local MESSAGE
    local BAP
    local BRANCH #------not used?
    local COMMIT
    local DATA
    local TEXT
    MESSAGE="$(cat "${MSG_FILE}")"
    BAP="$(cat "${BAP_VERSION_FILE}")"
    COMMIT="$(sed -z -e 's/\n/\\n/g' -e 's/\"/\\"/g' "${GIT_COMMIT_FILE}")"
    #replace \n, \", '\'' and '\`' with \\n, \\", '\'' and '\`' respectively  
    DATA="$(sed -z \
        -e 's/\n/\\n/g' \
        -e 's/\"/\\"/g' \
        -e 's/'\''/\'\''/g' \
        -e 's/'\`'/'\`'/g' \
        "${REPORT_FILE}")"
    TEXT="STATUS: ${MESSAGE}"
    TEXT="${TEXT}\nBAP: ${BAP}"
    TEXT="${TEXT}\nCOMMIT:\n\`\`\`\n${COMMIT}\n\`\`\`"
    TEXT="${TEXT}\nOUTPUT:\n\`\`\`\n${DATA}\n\`\`\`"
    echo "{
        \"username\":\"${SLACK_USERNAME}\",
        \"text\":\"${TEXT}\"
    }" > "${SLACK_FILE}"
}

#DESC: Prints the payload created in build_slack_payload 
print_payload () {
    echo "printing payload:"
    echo "MESSAGE: ${MESSAGE}"
    echo "BAP: ${BAP}"
    echo "BRANCH: ${BRANCH}"
    echo "COMMIT: ${COMMIT}"
    echo "DATA: ${DATA}"
    echo "TEXT: ${TEXT}"
}

# DESC: Posts a message to slack
# OUTPUT: The exit code of the curl/POST command
post_to_slack () {
    local OUTPUT
    local RESULT 
    OUTPUT="$(curl \
       	  --http1.1 \
    	  -X POST \
    	  -H "Content type: application/json" \
    	  -d @"${SLACK_FILE}" \
    	  "${SLACK_URL}")"
    RESULT=${?}
    echo "${OUTPUT}"
    return ${RESULT}
}

# DESC: Reports the current status to slack
# OUTPUT: Exit code of the attempt to send status to slack
report_to_slack () {
    build_slack_payload
    print_payload
    post_to_slack
}

