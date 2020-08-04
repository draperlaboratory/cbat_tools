#include <stdlib.h>

int main() {

    // Allocate a byte of memory, at address `addr`
    char *addr = malloc(sizeof(char));

    // Don't proceed if we got no address
    if (addr == NULL) { return 0; }

    // Store the character 'z' at that address
    *addr = 'z';

}
