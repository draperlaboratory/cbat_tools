#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

/* This function checks a solution to the 4-rooks problem:
 * on a 4x4 chess board, place 4 rooks in positions where none of them
 * can be captured by any of the others in a single move.
 *
 * The solution must be encoded as a 16-bit integer, indexed like this:
 *
 *     0b[0][1][2][3][4][5][6][7][8][9][10][11][12][13][14][16]
 *
 * Each bit represents a position on a 4x4 board, going from the top to
 * the bottom, left to right. 
 *
 * If a bit in the solution is 1, that indicates that a rook goes there.
 * For example, take this 16-bit binary integer (hex 0x4281):
 *
 *     0b1000 0010 0100 0001
 *
 * That integer represents a board like this:
 *
 *     1 0 0 0
 *     0 0 1 0
 *     0 1 0 0
 *     0 0 0 1
 *
 * If the proposed board is a solution to the problem, this function will
 * trip an assert. Otherwise, it returns 0.
 */
int check(uint16_t board) {

    // Extract each bit to get each board position
    bool r0 = (board >> 0) & 1;
    bool r1 = (board >> 1) & 1;
    bool r2 = (board >> 2) & 1;
    bool r3 = (board >> 3) & 1;
    bool r4 = (board >> 4) & 1;
    bool r5 = (board >> 5) & 1;
    bool r6 = (board >> 6) & 1;
    bool r7 = (board >> 7) & 1;
    bool r8 = (board >> 8) & 1;
    bool r9 = (board >> 9) & 1;
    bool r10 = (board >> 10) & 1;
    bool r11 = (board >> 11) & 1;
    bool r12 = (board >> 12) & 1;
    bool r13 = (board >> 13) & 1;
    bool r14 = (board >> 14) & 1;
    bool r15 = (board >> 15) & 1;

    // Print the board for good measure
    printf("%d  %d  %d  %d\n", r0, r1, r2, r3);
    printf("%d  %d  %d  %d\n", r4, r5, r6, r7);
    printf("%d  %d  %d  %d\n", r8, r9, r10, r11);
    printf("%d  %d  %d  %d\n", r12, r13, r14, r15);

    // Assume the board is correct (we'll falsify it if we can below)
    bool correct = true;

    // There must be exactly 4 rooks 
    uint8_t num_rooks = r0 + r1 + r2 + r3 \
                      + r4 + r5 + r6 + r7 \
                      + r8 + r9 + r10 + r11 \
                      + r12 + r13 + r14 + r15;
    if (num_rooks != 4) { correct = false; }

    // There cannot be more than 1 rook in row 0
    if (r0 + r1 + r2 + r3 > 1) { correct = false; }

    // There cannot be more than 1 rook in row 1
    if (r4 + r5 + r6 + r7 > 1) { correct = false; }

    // There cannot be more than 1 rook in row 2
    if (r8 + r9 + r10 + r11 > 1) { correct = false; }

    // There cannot be more than 1 rook in row 3
    if (r12 + r13 + r14 + r15 > 1) { correct = false; }

    // There cannot be more than 1 rook in column 0
    if (r0 + r4 + r8 + r12 > 1) { correct = false; }

    // There cannot be more than 1 rook in column 1
    if (r1 + r5 + r9 + r13 > 1) { correct = false; }

    // There cannot be more than 1 rook in column 2
    if (r2 + r6 + r10 + r14 > 1) { correct = false; }

    // There cannot be more than 1 rook in column 3
    if (r3 + r7 + r11 + r15 > 1) { correct = false; }

    // Trip an assert if the solution hasn't been falsified
    if(correct){
        assert(0);
    }

    return 0;

}

/* The main entry point to the program. 
 *
 * This program expects the user to provide one command line argument:
 * a hex string, e.g., "0x4281". This is the hex version of a solution
 * to the 4-rooks problem (see the `check` function above). The hex string
 * is converted into a 16-bit integer, and passed to the `check` function.
 */
int main(int argc, char **argv) {

    // Convert the first argument (a hex string) to a 16-bit number
    const char *hexstring = argv[1];
    uint16_t board = (int)strtol(hexstring, NULL, 0);

    // Check the solution	
    return check(board);

}

