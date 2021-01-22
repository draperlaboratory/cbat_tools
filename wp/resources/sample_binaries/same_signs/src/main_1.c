#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

bool same_signs(int x, int y) {
    // When x is negative
    if(x < 0){
        // They have the same sign if x is negative too
        if (y < 0) { return true; }
        else { return false; }
    // When x is positive
    } else{
        // They have the same sign if y is positive too
        if (y >= 0) { return true; }
        else { return false; }
    }
}

int main() {
    // Try it out
    int x = 10;
    int y = -10;
    fputs(same_signs(x, y) ? "true\n" : "false\n", stdout);
    return 0;
}
