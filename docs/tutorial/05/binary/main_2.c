#include <stdio.h>

/* Different types of signals */
typedef enum {SURFACE, NAV, DEPLOY} signal_t;

/* Stubbed handler for the SURFACE signal */
int surface() {
    int status_code = 1;
    // Handle surfacing...
    return status_code;
}

/* Stubbed handler for the NAV signal */
int alter_course() {
    int status_code = 2;
    // Handle navigation...
    return status_code;
}

/* Stubbed handler for the DEPLOY signal */
int deploy_payload() {
    int status_code = 4;
    // Deploy the payload...
    return status_code;
}

/* Process a signal, and dispatch to an appropriate handler */
int process_signal(signal_t signal) {

    int status_code = 0;

    switch (signal) {
        case SURFACE:
            status_code = surface();
	    break;

        case NAV:
            status_code = alter_course();

        case DEPLOY:
            status_code = deploy_payload();
            break;
    }

    return status_code;

}

int main() {

    // Try it out
    signal_t signal = NAV;
    process_signal(signal);

    return 0;

}
