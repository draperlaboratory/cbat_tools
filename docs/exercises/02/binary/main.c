#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

/* This checks if the provided solution to a 3x3 sudoku puzzle is correct.
 *
 * The argument `solution` is a 32 bit integer, where every 2 bits indicate
 * a value at a position on the board. 
 *
 * The first 18 bits are used in the integer, starting from the left and 
 * moving to the right (and the other 14 bits in the integer are ignored). 
 *
 * For example:
 *
 *   +---+---+---+
 *   | 1 | 3 | 2 |  =>  01 11 10
 *   +---+---+---+
 *   | 2 | 1 | 3 |  =>  10 01 11  =>  011110 100111 111001 00000000000000
 *   +---+---+---+
 *   | 3 | 2 | 1 |  =>  11 10 01
 *   +---+---+---+
 *
 *   The number 01111010011111100100000000000000 is 0x7a7e4000 in hex.
 *
 *   If the provided solution is correct, this function trips an assert.
 */
int check(uint32_t solution) {

    char p8 = (solution >> (2 * 7)) & 0x3;
    char p7 = (solution >> (2 * 8)) & 0x3;
    char p6 = (solution >> (2 * 9)) & 0x3;
    char p5 = (solution >> (2 * 10)) & 0x3;
    char p4 = (solution >> (2 * 11)) & 0x3;
    char p3 = (solution >> (2 * 12)) & 0x3;
    char p2 = (solution >> (2 * 13)) & 0x3;
    char p1 = (solution >> (2 * 14)) & 0x3;
    char p0 = (solution >> (2 * 15)) & 0x3;

    printf("+---+---+---+\n");
    printf("| %d | %d | %d |\n", p0, p1, p2);
    printf("+---+---+---+\n");
    printf("| %d | %d | %d |\n", p3, p4, p5);
    printf("+---+---+---+\n");
    printf("| %d | %d | %d |\n", p6, p7, p8);
    printf("+---+---+---+\n");

    bool correct = true;

    if (p0 == p1 || p1 == p2 || p0 == p2) { correct = false; }
    else if (p3 == p4 || p4 == p5 || p3 == p5) { correct = false; }
    else if (p6 == p7 || p7 == p8 || p6 == p8) { correct = false; }

    else if (p0 == p3 || p3 == p6 || p0 == p6) { correct = false; }
    else if (p1 == p4 || p4 == p7 || p1 == p7) { correct = false; }
    else if (p2 == p5 || p5 == p8 || p2 == p8) { correct = false; }

    else if (p0 + p1 + p2 != 6) { correct = false; }
    else if (p3 + p4 + p5 != 6) { correct = false; }
    else if (p6 + p7 + p8 != 6) { correct = false; }

    else if (p0 + p3 + p6 != 6) { correct = false; }
    else if (p1 + p4 + p7 != 6) { correct = false; }
    else if (p2 + p5 + p8 != 6) { correct = false; }

    if (correct) {
        assert(0);
    }

    return correct;

}

/* The main entry point to the program. 
 *
 * This program expects the user to provide one command line argument:
 * a hex string, e.g., "0x7a7e4000". This is the hex version of a solution
 * to a 3x3 sudoku board. This hex string is converted into a 32-bit
 * integer, and passed to the `check` function.
 */
int main(int argc, char **argv) {

    // Convert the first argument (a hex string) to a 32-bit number
    const char *hexstring = argv[1];
    uint32_t solution = (int) strtol(hexstring, NULL, 0);

    // Check the solution	
    return !check(solution);

}

