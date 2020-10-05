#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

// the length of one side of the board
// note that changing this also requires changing the loop unrolling pragmas
// this is unfortunately necessary because gcc won't
// compile when it has to expand a macro inside a pragma

#ifndef BOARD_SIZE
#define BOARD_SIZE 8
#endif

#define WORDSIZE 64

#define GET_ELEMENT(boards, index)                                             \
  (boards[index / WORDSIZE] >> (index - WORDSIZE * (index / WORDSIZE)))

// the encoding of a n by n chessboard (where n is an integer
// less that or equal to 19) into an array of 64 bit integers
// where the less significant bit represents whether or not there
// is a queen on that index in the chessboard
int encode_nqueens(int64_t board_0, uint64_t board_1, uint64_t board_2,
                   uint64_t board_3, uint64_t board_4, uint64_t board_5) {

  int64_t board[6] = {board_0, board_1, board_2, board_3, board_4, board_5};

  // we encode the nqueen game constraints into this "correct" boolean
  bool correct = true;
#pragma clang loop unroll(full)
  for (int i = 0; i < BOARD_SIZE; i++) {
    // encode column and row constraints
    uint8_t row = 0;
    uint8_t col = 0;
    // encode in count of number of queens for
    // i above and below the main right and left diagonals
    uint8_t diag_r_1 = 0;
    uint8_t diag_r_2 = 0;
    uint8_t diag_l_1 = 0;
    uint8_t diag_l_2 = 0;
#pragma clang loop unroll(full)
    for (int j = 0; j < BOARD_SIZE; j++) {
      row += GET_ELEMENT(board, (BOARD_SIZE * i + j)) & 1;
      col += GET_ELEMENT(board, (BOARD_SIZE * j + i)) & 1;
      if (j < BOARD_SIZE - i) {
        // check if there's a queen at spot j on the ith diag above/below the
        // left/right diag
        diag_r_1 += GET_ELEMENT(board, (i + (BOARD_SIZE + 1) * j)) & 1;
        diag_r_2 +=
            GET_ELEMENT(board, (BOARD_SIZE * i + (BOARD_SIZE + 1) * j)) & 1;
        diag_l_1 +=
            GET_ELEMENT(board, (BOARD_SIZE * i + (BOARD_SIZE - 1) * (j + 1))) &
            1;
        diag_l_2 +=
            GET_ELEMENT(board, ((BOARD_SIZE - 1) + j * (BOARD_SIZE - 1) - i)) &
            1;
      }
    }
    // ensure that only one (or really an odd number that is forced to be one)
    // queen is observed in row i and col i
    // ensure that there is at most 1 queen on these diagonals
    // (the row and col constraints force there to be n total queens)
    correct &= (row == 1) && (col == 1) && (diag_r_1 <= 1) && (diag_r_2 <= 1) &&
               (diag_l_1 <= 1) && (diag_l_2 <= 1);
  }

  // only if the constraint we've encoded the nqueens game into can be satisfied
  // shall we trip a failing assert. The result is returned by CBAT's
  // countermodel.
  if (correct) {
    assert(0);
  }

  return 0;
}

// feed in a board represented as a 64 bit integer, and this will print out
// the board
void pretty_print_board(int64_t *board) {
  printf("\n");
  for (int row = 0; row < BOARD_SIZE; row++) {
    for (int col = 0; col < BOARD_SIZE; col++) {
      // if element is set, print Q otherwise print _
      if (GET_ELEMENT(board, (row * BOARD_SIZE + col)) & 1) {
        printf("Q");
      } else {
        printf("x");
      }
    }
    printf("\n");
  }
}

int main(int argc, char **argv) {
  int64_t board[6] = {
      0x4200040100008002, 0x0008000180002000, 0x0000000000000104, 0, 0, 0};
  pretty_print_board(board);
  encode_nqueens(0x4200040100008002, 0x0008000180002000, 0x0000000000000104, 0,
                 0, 0);
  return 0;
}
