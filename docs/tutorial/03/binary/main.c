#include <stdlib.h>

int main() {

    // Allocate a byte of memory, at address `addr`
    char *addr = malloc(sizeof(char));

    // Store the character 'z' at that address
    *addr = 'z';

}
