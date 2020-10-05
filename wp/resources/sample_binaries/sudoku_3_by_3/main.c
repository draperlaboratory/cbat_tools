#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

// mask of size 4 requires 4 bits
#define MASK_SIZE 0x4
#define MASK 0xf
#define WIDTH 0x9
#define REG_SIZE 64

#define GET_ELEMENT(boards, index)                                             \
  ((boards[(index * MASK_SIZE) / REG_SIZE] >>                                  \
    ((index * MASK_SIZE) - (((index * MASK_SIZE) / REG_SIZE) * REG_SIZE))) &   \
   MASK)

void print_board(int64_t board_0, int64_t board_1, int64_t board_2,
                 int64_t board_3, int64_t board_4, int64_t board_5) {
  int64_t board[6] = {board_0, board_1, board_2, board_3, board_4, board_5};
  for (int row = 0; row < WIDTH; row++) {
    for (int col = 0; col < WIDTH; col++) {
      printf(" %lx ", GET_ELEMENT(board, (row * WIDTH + col)));
    }
    printf("\n");
  }
}

void sudoku_solver(int64_t w_0, int64_t w_1, int64_t w_2, int64_t w_3,
                   int64_t w_4, int64_t w_5) {
  int64_t board[6] = {w_0, w_1, w_2, w_3, w_4, w_5};

  // sample puzzle encoding

  // row 0
  bool init_c_0 = GET_ELEMENT(board, 0) == 2;
  bool init_c_1 = GET_ELEMENT(board, 1) == 4;
  bool init_c_2 = GET_ELEMENT(board, 2) == 7;
  bool init_c_3 = GET_ELEMENT(board, 4) == 0;
  bool init_c_4 = GET_ELEMENT(board, 5) == 1;
  bool init_c_5 = GET_ELEMENT(board, 7) == 6;
  bool init_c_6 = GET_ELEMENT(board, 8) == 8;

  // row 1
  bool init_c_7 = GET_ELEMENT(board, 9) == 1;
  bool init_c_8 = GET_ELEMENT(board, 11) == 5;
  bool init_c_9 = GET_ELEMENT(board, 12) == 7;
  bool init_c_10 = GET_ELEMENT(board, 13) == 6;
  bool init_c_11 = GET_ELEMENT(board, 15) == 3;

  // row 2
  bool init_c_12 = GET_ELEMENT(board, 18) == 8;
  bool init_c_13 = GET_ELEMENT(board, 19) == 6;
  bool init_c_14 = GET_ELEMENT(board, 21) == 4;
  bool init_c_15 = GET_ELEMENT(board, 26) == 7;

  // row 3
  bool init_c_16 = GET_ELEMENT(board, 27) == 0;
  bool init_c_17 = GET_ELEMENT(board, 30) == 2;
  bool init_c_18 = GET_ELEMENT(board, 32) == 6;

  // row 4
  bool init_c_19 = GET_ELEMENT(board, 39) == 0;
  bool init_c_20 = GET_ELEMENT(board, 40) == 4;
  bool init_c_21 = GET_ELEMENT(board, 41) == 7;
  bool init_c_22 = GET_ELEMENT(board, 42) == 6;
  bool init_c_23 = GET_ELEMENT(board, 43) == 8;

  // row 5
  bool init_c_24 = GET_ELEMENT(board, 45) == 6;
  bool init_c_25 = GET_ELEMENT(board, 47) == 4;
  bool init_c_26 = GET_ELEMENT(board, 49) == 5;
  bool init_c_27 = GET_ELEMENT(board, 52) == 1;
  bool init_c_28 = GET_ELEMENT(board, 53) == 0;

  // row 6
  bool init_c_29 = GET_ELEMENT(board, 54) == 7;
  bool init_c_30 = GET_ELEMENT(board, 58) == 3;
  bool init_c_31 = GET_ELEMENT(board, 60) == 0;
  bool init_c_32 = GET_ELEMENT(board, 61) == 2;

  // row 7
  bool init_c_33 = GET_ELEMENT(board, 63) == 4;
  bool init_c_34 = GET_ELEMENT(board, 65) == 0;
  bool init_c_35 = GET_ELEMENT(board, 66) == 6;

  // row 8
  bool init_c_36 = GET_ELEMENT(board, 78) == 4;
  bool init_c_37 = GET_ELEMENT(board, 80) == 3;

  bool init_total = init_c_0 && init_c_1 && init_c_2 && init_c_3 && init_c_4 &&
                    init_c_5 && init_c_6 && init_c_7 && init_c_8 && init_c_9 &&
                    init_c_10 && init_c_11 && init_c_12 && init_c_13 &&
                    init_c_14 && init_c_15 && init_c_16 && init_c_17 &&
                    init_c_18 && init_c_19 && init_c_20 && init_c_21 &&
                    init_c_22 && init_c_23 && init_c_24 && init_c_25 &&
                    init_c_26 && init_c_27 && init_c_28 && init_c_29 &&
                    init_c_30 && init_c_31 && init_c_32 && init_c_33 &&
                    init_c_34 && init_c_35 && init_c_36 && init_c_37;

  bool row_constr = true, col_constr = true, sq_constr = true;

  // iterate through all possible values and assert that each row/col must
  // contain exactly one of each number
#pragma clang loop unroll(full)
  for (int64_t k = 0; k < WIDTH; k++) {
#pragma clang loop unroll(full)
    for (int64_t i = 0; i < WIDTH; i++) {
      bool single_row_constr = false, single_col_constr = false;
#pragma clang loop unroll(full)
      for (int64_t j = 0; j < WIDTH; j++) {
        single_row_constr ^= GET_ELEMENT(board, (i * WIDTH + j)) == k;
        single_col_constr ^= GET_ELEMENT(board, (i + j * WIDTH)) == k;
      }
      row_constr &= single_row_constr;
      col_constr &= single_col_constr;
    }
  }

#pragma clang loop unroll(full)
  for (int64_t k = 0; k < WIDTH; k++) {
#pragma clang loop unroll(full)
    for (int64_t sq_idx = 0; sq_idx < WIDTH; sq_idx++) {
      // for each k, construct constraint saying "only contains one of k"
      bool single_sq_constr = false;
#pragma clang loop unroll(full)
      for (int64_t cell_idx = 0; cell_idx < WIDTH; cell_idx++) {
        switch (sq_idx) {
        case 0:
          switch (cell_idx) {
          case 0:
            single_sq_constr ^= GET_ELEMENT(board, 0) == k;
            break;
          case 1:
            single_sq_constr ^= GET_ELEMENT(board, 1) == k;
            break;
          case 2:
            single_sq_constr ^= GET_ELEMENT(board, 2) == k;
            break;
          case 3:
            single_sq_constr ^= GET_ELEMENT(board, 9) == k;
            break;
          case 4:
            single_sq_constr ^= GET_ELEMENT(board, 10) == k;
            break;
          case 5:
            single_sq_constr ^= GET_ELEMENT(board, 11) == k;
            break;
          case 6:
            single_sq_constr ^= GET_ELEMENT(board, 18) == k;
            break;
          case 7:
            single_sq_constr ^= GET_ELEMENT(board, 19) == k;
            break;
          case 8:
            single_sq_constr ^= GET_ELEMENT(board, 20) == k;
            break;
          }
          break;
        case 1:
          switch (cell_idx) {
          case 0:
            single_sq_constr ^= GET_ELEMENT(board, 3) == k;
            break;
          case 1:
            single_sq_constr ^= GET_ELEMENT(board, 4) == k;
            break;
          case 2:
            single_sq_constr ^= GET_ELEMENT(board, 5) == k;
            break;
          case 3:
            single_sq_constr ^= GET_ELEMENT(board, 12) == k;
            break;
          case 4:
            single_sq_constr ^= GET_ELEMENT(board, 13) == k;
            break;
          case 5:
            single_sq_constr ^= GET_ELEMENT(board, 14) == k;
            break;
          case 6:
            single_sq_constr ^= GET_ELEMENT(board, 21) == k;
            break;
          case 7:
            single_sq_constr ^= GET_ELEMENT(board, 22) == k;
            break;
          case 8:
            single_sq_constr ^= GET_ELEMENT(board, 23) == k;
            break;
          }
          break;
        case 2:
          switch (cell_idx) {
          case 0:
            single_sq_constr ^= GET_ELEMENT(board, 6) == k;
            break;
          case 1:
            single_sq_constr ^= GET_ELEMENT(board, 7) == k;
            break;
          case 2:
            single_sq_constr ^= GET_ELEMENT(board, 8) == k;
            break;
          case 3:
            single_sq_constr ^= GET_ELEMENT(board, 15) == k;
            break;
          case 4:
            single_sq_constr ^= GET_ELEMENT(board, 16) == k;
            break;
          case 5:
            single_sq_constr ^= GET_ELEMENT(board, 17) == k;
            break;
          case 6:
            single_sq_constr ^= GET_ELEMENT(board, 24) == k;
            break;
          case 7:
            single_sq_constr ^= GET_ELEMENT(board, 25) == k;
            break;
          case 8:
            single_sq_constr ^= GET_ELEMENT(board, 26) == k;
            break;
          }
          break;
        case 3:
          switch (cell_idx) {
          case 0:
            single_sq_constr ^= GET_ELEMENT(board, 27) == k;
            break;
          case 1:
            single_sq_constr ^= GET_ELEMENT(board, 28) == k;
            break;
          case 2:
            single_sq_constr ^= GET_ELEMENT(board, 29) == k;
            break;
          case 3:
            single_sq_constr ^= GET_ELEMENT(board, 36) == k;
            break;
          case 4:
            single_sq_constr ^= GET_ELEMENT(board, 37) == k;
            break;
          case 5:
            single_sq_constr ^= GET_ELEMENT(board, 38) == k;
            break;
          case 6:
            single_sq_constr ^= GET_ELEMENT(board, 45) == k;
            break;
          case 7:
            single_sq_constr ^= GET_ELEMENT(board, 46) == k;
            break;
          case 8:
            single_sq_constr ^= GET_ELEMENT(board, 47) == k;
            break;
          }
          break;
        case 4:
          switch (cell_idx) {
          case 0:
            single_sq_constr ^= GET_ELEMENT(board, 30) == k;
            break;
          case 1:
            single_sq_constr ^= GET_ELEMENT(board, 31) == k;
            break;
          case 2:
            single_sq_constr ^= GET_ELEMENT(board, 32) == k;
            break;
          case 3:
            single_sq_constr ^= GET_ELEMENT(board, 39) == k;
            break;
          case 4:
            single_sq_constr ^= GET_ELEMENT(board, 40) == k;
            break;
          case 5:
            single_sq_constr ^= GET_ELEMENT(board, 41) == k;
            break;
          case 6:
            single_sq_constr ^= GET_ELEMENT(board, 48) == k;
            break;
          case 7:
            single_sq_constr ^= GET_ELEMENT(board, 49) == k;
            break;
          case 8:
            single_sq_constr ^= GET_ELEMENT(board, 50) == k;
            break;
          }
          break;
        case 5:
          switch (cell_idx) {
          case 0:
            single_sq_constr ^= GET_ELEMENT(board, 33) == k;
            break;
          case 1:
            single_sq_constr ^= GET_ELEMENT(board, 34) == k;
            break;
          case 2:
            single_sq_constr ^= GET_ELEMENT(board, 35) == k;
            break;
          case 3:
            single_sq_constr ^= GET_ELEMENT(board, 42) == k;
            break;
          case 4:
            single_sq_constr ^= GET_ELEMENT(board, 43) == k;
            break;
          case 5:
            single_sq_constr ^= GET_ELEMENT(board, 44) == k;
            break;
          case 6:
            single_sq_constr ^= GET_ELEMENT(board, 51) == k;
            break;
          case 7:
            single_sq_constr ^= GET_ELEMENT(board, 52) == k;
            break;
          case 8:
            single_sq_constr ^= GET_ELEMENT(board, 53) == k;
            break;
          }
          break;
        case 6:
          switch (cell_idx) {
          case 0:
            single_sq_constr ^= GET_ELEMENT(board, 54) == k;
            break;
          case 1:
            single_sq_constr ^= GET_ELEMENT(board, 55) == k;
            break;
          case 2:
            single_sq_constr ^= GET_ELEMENT(board, 56) == k;
            break;
          case 3:
            single_sq_constr ^= GET_ELEMENT(board, 63) == k;
            break;
          case 4:
            single_sq_constr ^= GET_ELEMENT(board, 64) == k;
            break;
          case 5:
            single_sq_constr ^= GET_ELEMENT(board, 65) == k;
            break;
          case 6:
            single_sq_constr ^= GET_ELEMENT(board, 72) == k;
            break;
          case 7:
            single_sq_constr ^= GET_ELEMENT(board, 73) == k;
            break;
          case 8:
            single_sq_constr ^= GET_ELEMENT(board, 74) == k;
            break;
          }
          break;
        case 7:
          switch (cell_idx) {
          case 0:
            single_sq_constr ^= GET_ELEMENT(board, 57) == k;
            break;
          case 1:
            single_sq_constr ^= GET_ELEMENT(board, 58) == k;
            break;
          case 2:
            single_sq_constr ^= GET_ELEMENT(board, 59) == k;
            break;
          case 3:
            single_sq_constr ^= GET_ELEMENT(board, 66) == k;
            break;
          case 4:
            single_sq_constr ^= GET_ELEMENT(board, 67) == k;
            break;
          case 5:
            single_sq_constr ^= GET_ELEMENT(board, 68) == k;
            break;
          case 6:
            single_sq_constr ^= GET_ELEMENT(board, 75) == k;
            break;
          case 7:
            single_sq_constr ^= GET_ELEMENT(board, 76) == k;
            break;
          case 8:
            single_sq_constr ^= GET_ELEMENT(board, 77) == k;
            break;
          }
          break;
        case 8:
          switch (cell_idx) {
          case 0:
            single_sq_constr ^= GET_ELEMENT(board, 60) == k;
            break;
          case 1:
            single_sq_constr ^= GET_ELEMENT(board, 61) == k;
            break;
          case 2:
            single_sq_constr ^= GET_ELEMENT(board, 62) == k;
            break;
          case 3:
            single_sq_constr ^= GET_ELEMENT(board, 69) == k;
            break;
          case 4:
            single_sq_constr ^= GET_ELEMENT(board, 70) == k;
            break;
          case 5:
            single_sq_constr ^= GET_ELEMENT(board, 71) == k;
            break;
          case 6:
            single_sq_constr ^= GET_ELEMENT(board, 78) == k;
            break;
          case 7:
            single_sq_constr ^= GET_ELEMENT(board, 79) == k;
            break;
          case 8:
            single_sq_constr ^= GET_ELEMENT(board, 80) == k;
            break;
          }
          break;
        }
      }
      sq_constr &= single_sq_constr;
    }
  }

  if (init_total && sq_constr && row_constr && col_constr) {
    assert(0);
  }
}

int main(int argc, char **argv) {
  print_board(0x3867501865103742, 0x1285070152436824, 0x4765867402134376,
              0x4620435187012358, 0x7408162515827603, 0x3);
  sudoku_solver(0x3867501865103742, 0x1285070152436824, 0x4765867402134376,
                0x4620435187012358, 0x7408162515827603, 0x3);
  return 0;
}
