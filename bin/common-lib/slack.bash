# -------------------------------
#
# Utilities for slack integration
#
# -------------------------------

# Food for thought: how to check if var is und
# Idea: is it empty string?
# -z asks env to see if proceeding is empty string
# will return 1 if so, o.t. 0 (aka good)


# DESC:
# INPUT:
# OUTPUT:
there_is_a_SLACK_USERNAME () {
    if [ -z "${SLACK_USERNAME}" ];
    then return 1;
    else return 0;
    fi
}

# DESC:
# INPUT:
# OUTPUT:
there_is_a_SLACK_URL () {
    if [ -z "${SLACK_URL}" ];
    then return 1;
    else return 0;
    fi
}

# DESC:
# INPUT:
# OUTPUT:
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

# DESC: Post a message to slack
# INPUT: - 
# OUTPUT: The exit code of the curl/POST status
post_to_slack () {
    local OUTPUT
    local RESULT #------what's the difference between an output and result?
    #------ curl (client url) allows you to communicate with a server
    OUTPUT="$(curl \
    	  -X POST \
    	  -H "Content type: application/json" \
    	  -d @"${SLACK_FILE}" \
    	  "${SLACK_URL}")"
    RESULT=${?}
    echo "${OUTPUT}"
    return ${RESULT}
}


# DESC:
# INPUT:
# OUTPUT:
report_to_slack () {
    build_slack_payload
    post_to_slack
}

