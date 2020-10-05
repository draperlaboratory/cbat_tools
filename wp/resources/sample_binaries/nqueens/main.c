#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

// the length of one side of the board
// note that changing this also requires changing the loop unrolling pragmas
// this is unfortunately necessary because gcc won't
// compile when it has to expand a macro inside a pragma

#define STRINGIFY(a) #a
#ifndef BOARD_SIZE
#define BOARD_SIZE 8
#endif
#define GET_ELEMENT(boards, index)                                             \
  (boards[index / 64] >> (index - 64 * (index / 64)))

int encode_nqueens_net(int64_t board_0, uint64_t board_1, uint64_t board_2,
                       uint64_t board_3, uint64_t board_4, uint64_t board_5) {

  int64_t board[6] = {board_0, board_1, board_2, board_3, board_4, board_5};

  // we encode the nqueen game constraints into this "correct" boolean
  bool correct = true;
#pragma clang loop unroll(full)
  for (int i = 0; i < BOARD_SIZE; i++) {
    uint8_t row = 0;
    uint8_t col = 0;
    uint8_t diag_r_1 = 0;
    uint8_t diag_r_2 = 0;
    uint8_t diag_l_1 = 0;
    uint8_t diag_l_2 = 0;
#pragma clang loop unroll(full)
    for (int j = 0; j < BOARD_SIZE; j++) {
      row += GET_ELEMENT(board, (BOARD_SIZE * i + j)) & 1;
      col += GET_ELEMENT(board, (BOARD_SIZE * j + i)) & 1;
      if (j < BOARD_SIZE - i) {
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
    correct &= (row == 1) && (col == 1) && (diag_r_1 <= 1) && (diag_r_2 <= 1) &&
               (diag_l_1 <= 1) && (diag_l_2 <= 1);
  }

  // only if the constraint we've encoded the nqueens game into can be satisfied
  // shall we trip a failing assert. The result is returned by CBAT in RDI.
  if (correct) {
    assert(0);
  }

  return 0;
}

bool f_row(int64_t board_0, uint64_t board_1, uint64_t board_2,
           uint64_t board_3);
bool f_row(int64_t board_0, uint64_t board_1, uint64_t board_2,
           uint64_t board_3) {
  int64_t board[4] = {board_0, board_1, board_2, board_3};
  bool correct = true;
  for (int i = 0; i < BOARD_SIZE; i++) {
    uint8_t row = 0;
    for (int j = 0; j < BOARD_SIZE; j++) {
      row += GET_ELEMENT(board, (BOARD_SIZE * i + j)) & 1;
    }
    correct &= (row == 1);
  }
  return correct;
}

bool f_col(int64_t board_0, uint64_t board_1, uint64_t board_2,
           uint64_t board_3);
bool f_col(int64_t board_0, uint64_t board_1, uint64_t board_2,
           uint64_t board_3) {
  int64_t board[4] = {board_0, board_1, board_2, board_3};
  bool correct = true;
  for (int i = 0; i < BOARD_SIZE; i++) {
    uint8_t col = 0;
    for (int j = 0; j < BOARD_SIZE; j++) {
      col += GET_ELEMENT(board, (BOARD_SIZE * j + i)) & 1;
    }
    correct &= (col == 1);
  }
  return correct;
}

bool f_diag_r_1(int64_t board_0, uint64_t board_1, uint64_t board_2,
                uint64_t board_3);
bool f_diag_r_1(int64_t board_0, uint64_t board_1, uint64_t board_2,
                uint64_t board_3) {
  int64_t board[4] = {board_0, board_1, board_2, board_3};
  bool correct = true;
  for (int i = 0; i < BOARD_SIZE; i++) {
    uint8_t diag_r_1 = 0;
    for (int j = 0; j < BOARD_SIZE; j++) {
      if (j < BOARD_SIZE - i) {
        diag_r_1 += GET_ELEMENT(board, (i + (BOARD_SIZE + 1) * j)) & 1;
      }
    }
    correct &= (diag_r_1 <= 1);
  }
  return correct;
}

bool f_diag_r_2(int64_t board_0, uint64_t board_1, uint64_t board_2,
                uint64_t board_3);
bool f_diag_r_2(int64_t board_0, uint64_t board_1, uint64_t board_2,
                uint64_t board_3) {
  int64_t board[4] = {board_0, board_1, board_2, board_3};
  bool correct = true;
  for (int i = 0; i < BOARD_SIZE; i++) {
    uint8_t diag_r_2 = 0;
    for (int j = 0; j < BOARD_SIZE; j++) {
      if (j < BOARD_SIZE - i) {
        diag_r_2 +=
            GET_ELEMENT(board, (BOARD_SIZE * i + (BOARD_SIZE + 1) * j)) & 1;
      }
    }
    correct &= (diag_r_2 <= 1);
  }
  return correct;
}

bool f_diag_l_1(int64_t board_0, uint64_t board_1, uint64_t board_2,
                uint64_t board_3);
bool f_diag_l_1(int64_t board_0, uint64_t board_1, uint64_t board_2,
                uint64_t board_3) {
  int64_t board[4] = {board_0, board_1, board_2, board_3};
  bool correct = true;
  for (int i = 0; i < BOARD_SIZE; i++) {
    uint8_t diag_l_1 = 0;
    for (int j = 0; j < BOARD_SIZE; j++) {
      if (j < BOARD_SIZE - i) {
        diag_l_1 +=
            GET_ELEMENT(board, (BOARD_SIZE * i + (BOARD_SIZE - 1) * (j + 1))) &
            1;
      }
    }
    correct &= (diag_l_1 <= 1);
  }
  return correct;
}

bool f_diag_l_2(int64_t board_0, uint64_t board_1, uint64_t board_2,
                uint64_t board_3);
bool f_diag_l_2(int64_t board_0, uint64_t board_1, uint64_t board_2,
                uint64_t board_3) {
  int64_t board[4] = {board_0, board_1, board_2, board_3};
  bool correct = true;
  for (int i = 0; i < BOARD_SIZE; i++) {
    uint8_t diag_l_2 = 0;
    for (int j = 0; j < BOARD_SIZE; j++) {
      if (j < BOARD_SIZE - i) {
        diag_l_2 +=
            GET_ELEMENT(board, ((BOARD_SIZE - 1) + j * (BOARD_SIZE - 1) - i)) &
            1;
      }
    }
    correct &= (diag_l_2 <= 1);
  }
  return correct;
}

// the encoding of a n by n chessboard (where n is an integer
// less that or equal to 16) into an array of 64 bit integers
// where the less significant bit represents whether or not there
// is a queen on that index in the chessboard
int encode_nqueens_split(int64_t board_0, uint64_t board_1, uint64_t board_2,
                         uint64_t board_3) {

  int64_t board[4] = {board_0, board_1, board_2, board_3};

  // we encode the nqueen game constraints into this "correct" boolean
  bool correct = true;
  for (int i = 0; i < BOARD_SIZE; i++) {
    uint8_t row = 0;
    for (int j = 0; j < BOARD_SIZE; j++) {
      row += GET_ELEMENT(board, (BOARD_SIZE * i + j)) & 1;
    }
    correct &= (row == 1);
  }
  for (int i = 0; i < BOARD_SIZE; i++) {
    uint8_t col = 0;
    for (int j = 0; j < BOARD_SIZE; j++) {
      col += GET_ELEMENT(board, (BOARD_SIZE * j + i)) & 1;
    }
    correct &= (col == 1);
  }
  for (int i = 0; i < BOARD_SIZE; i++) {
    uint8_t diag_r_1 = 0;
    for (int j = 0; j < BOARD_SIZE; j++) {
      if (j < BOARD_SIZE - i) {
        diag_r_1 += GET_ELEMENT(board, (i + (BOARD_SIZE + 1) * j)) & 1;
      }
    }
    correct &= (diag_r_1 <= 1);
  }
  for (int i = 0; i < BOARD_SIZE; i++) {
    uint8_t diag_r_2 = 0;
    for (int j = 0; j < BOARD_SIZE; j++) {
      if (j < BOARD_SIZE - i) {
        diag_r_2 +=
            GET_ELEMENT(board, (BOARD_SIZE * i + (BOARD_SIZE + 1) * j)) & 1;
      }
    }
    correct &= (diag_r_2 <= 1);
  }
  for (int i = 0; i < BOARD_SIZE; i++) {
    uint8_t diag_l_1 = 0;
    for (int j = 0; j < BOARD_SIZE; j++) {
      if (j < BOARD_SIZE - i) {
        diag_l_1 +=
            GET_ELEMENT(board, (BOARD_SIZE * i + (BOARD_SIZE - 1) * (j + 1))) &
            1;
      }
    }
    correct &= (diag_l_1 <= 1);
  }
  for (int i = 0; i < BOARD_SIZE; i++) {
    uint8_t diag_l_2 = 0;
    for (int j = 0; j < BOARD_SIZE; j++) {
      if (j < BOARD_SIZE - i) {
        diag_l_2 +=
            GET_ELEMENT(board, ((BOARD_SIZE - 1) + j * (BOARD_SIZE - 1) - i)) &
            1;
      }
    }
    correct &= (diag_l_2 <= 1);
  }

  // only if the constraint we've encoded the nqueens game into can be satisfied
  // shall we trip a failing assert. The result is returned by CBAT in RDI.
  if (correct) {
    assert(0);
  }

  return 0;
}

int encode_nqueens_2_split(int64_t board_0, uint64_t board_1, uint64_t board_2,
                           uint64_t board_3) {

  int64_t board[4] = {board_0, board_1, board_2, board_3};

  // we encode the nqueen game constraints into this "correct" boolean
  bool correct = true;
  for (int i = 0; i < BOARD_SIZE; i++) {
    uint8_t row = 0;
    uint8_t col = 0;
    for (int j = 0; j < BOARD_SIZE; j++) {
      row += GET_ELEMENT(board, (BOARD_SIZE * i + j)) & 1;
      col += GET_ELEMENT(board, (BOARD_SIZE * j + i)) & 1;
    }
    correct &= (row == 1) && (col == 1);
  }
  for (int i = 0; i < BOARD_SIZE; i++) {
    volatile uint8_t diag_r_1 = 0;
    volatile uint8_t diag_r_2 = 0;
    volatile uint8_t diag_l_1 = 0;
    volatile uint8_t diag_l_2 = 0;
    for (int j = 0; j < BOARD_SIZE; j++) {
      if (j < BOARD_SIZE - i) {
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
    correct &= (diag_r_1 <= 1) && (diag_r_2 <= 1) && (diag_l_1 <= 1) &&
               (diag_l_2 <= 1);
  }

  // only if the constraint we've encoded the nqueens game into can be satisfied
  // shall we trip a failing assert. The result is returned by CBAT in RDI.
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
  //int64_t board[6] = {0x4200040100008002, 0x0008000180002000, 0x0000000000000104, 0, 0, 0};
  //pretty_print_board(board);
  //encode_nqueens_net(0x4200040100008002, 0x0008000180002000, 0x0000000000000104, 0, 0, 0);
  return 0;
}
