#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

bool is_valid_ID(int empl_id) {

    bool correct = true;

    if (empl_id > 0xddddddef) {
        assert(0);
    }

    if (empl_id < 10051 || empl_id > 1000000) {
        correct = false;
    }

    return correct;

}

/* Check if the first argument provided to the command line
 * is a valid employee ID.
 */
int main(int argc, char *argv[]) {

    const char *user_input = argv[1];
    int employee_id = (int) strtol(user_input, NULL, 0);

    bool is_ok = is_valid_ID(employee_id);
    return !is_ok;

}
