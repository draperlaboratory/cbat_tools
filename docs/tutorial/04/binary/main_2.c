#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

bool same_signs(int x, int y) {
    return !((x ^ y) < 0);
}

int main() {

    // Try it out
    int x = 10;
    int y = -10;
    fputs(same_signs(x, y) ? "true\n" : "false\n", stdout);

    return 0;

}
