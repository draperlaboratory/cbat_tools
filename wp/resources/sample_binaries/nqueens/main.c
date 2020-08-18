#include <assert.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#pragma GCC push_options
#pragma GCC optimize ("unroll-loops")

// the length of one side of the board
// note that changing this also requires changing the loop unrolling pragmas
// this is unfortunately necessary because gcc won't
// compile when it has to expand a macro inside a pragma

#define STRINGIFY(a) #a
#define BOARD_SIZE 4
#define GET_ELEMENT(boards, index) (boards[index / 64] >> (index - 64 * (index / 64)))

// the encoding of a n by n chessboard (where n is an integer
// less that or equal to 16) into an array of 64 bit integers 
// where the less significant bit represents whether or not there 
// is a queen on that index in the chessboard
int encode_nqueens(int64_t board_0, uint64_t board_1, uint64_t board_2, uint64_t board_3) {

  int64_t board[4] = {board_0, board_1, board_2, board_3};

  // we encode the nqueen game constraints into this "correct" boolean
  bool correct = true;
  // encode column and row constraints
    for(int i = 0; i < BOARD_SIZE; i++){
      uint8_t row = 0;
      uint8_t col = 0;
      // ensure that only one (or really an odd number that is forced to be one)
      // queen is observed in row i and col i
        for(int j = 0; j < BOARD_SIZE; j++){
          // note that xor works here because even if you have an odd number of
          // trues then some other constraint will be violated
          col += GET_ELEMENT(board, (BOARD_SIZE * j + i)) & 1;
          row += GET_ELEMENT(board, (BOARD_SIZE * i + j)) & 1;
        }
      correct &= (row == 1) && (col == 1);
    }
  // diagonals constraints
    for(int i = 0; i < BOARD_SIZE; i++){
      // encode in count of number of queens for 
      // i above and below the main right and left diagonals
      uint8_t diag_r_1 = 0;
      uint8_t diag_r_2 = 0;
      uint8_t diag_l_1 = 0;
      uint8_t diag_l_2 = 0;
      // check if there's a queen at spot j on the ith diag above/below the
      // left/right diag
        for(int j = 0; j < BOARD_SIZE; j++){
          if(j < BOARD_SIZE - i){
            diag_r_1 += GET_ELEMENT(board, (i + (BOARD_SIZE + 1) * j)) & 1;
            diag_r_2 += GET_ELEMENT(board, (BOARD_SIZE * i + (BOARD_SIZE + 1) * j)) & 1;
            diag_l_1 += GET_ELEMENT(board, (BOARD_SIZE * i + (BOARD_SIZE - 1) * (j + 1))) & 1;
            diag_l_2 += GET_ELEMENT(board, ((BOARD_SIZE - 1) + j * (BOARD_SIZE - 1) - i )) & 1;
          }
        }
      // ensure that there is at most 1 queen on these diagonals
      // (the row and col constraints force there to be n total queens)
      correct &= (diag_r_1 <= 1) && (diag_r_2 <= 1) && (diag_l_1 <= 1) && (diag_l_2 <= 1);
    }

  // only if the constraint we've encoded the nqueens game into can be satisfied
  // shall we trip a failing assert. The result is returned by CBAT in RDI.
  if(correct){
    assert(0);
  }

  return 0;
}

// feed in a board represented as a 64 bit integer, and this will print out
// the board
void pretty_print_board(int64_t* board){
  printf("\n");
  for(int row = 0; row < BOARD_SIZE; row++){
    for(int col = 0; col < BOARD_SIZE; col++){
      // if element is set, print Q otherwise print _
      if(GET_ELEMENT(board, (row * BOARD_SIZE + col)) & 1){
        printf("Q");
      } else{
        printf("x");
      }
    }
    printf("\n");
  }
}

int main(int argc,char ** argv) {
  int64_t board[4] = {0x124048, 0, 0, 0};
  pretty_print_board(board);
  encode_nqueens(0x4182, 0x0, 0x0, 0x0);
}
