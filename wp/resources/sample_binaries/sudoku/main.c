#include <assert.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>

#pragma GCC push_options
#pragma GCC optimize ("unroll-loops")

#define GET_ELEMENT(index, input) (( (input) >> (2 * (index))) & 0x3)

void print_board(uint32_t board){
        for(int row = 0; row < 4; row++){
                for(int col = 0; col < 4; col++){
                        switch(GET_ELEMENT(row * 4 + col, board)){
                                case 0x0:
                                        printf(" 4 ");
                                        break;
                                case 0x1:
                                        printf(" 1 ");
                                        break;
                                case 0x2:
                                        printf(" 2 ");
                                        break;
                                case 0x3:
                                        printf(" 3 ");
                                        break;
                        }
                }
                printf("\n");
        }
}

void sudoku_solver(uint32_t input){
        // sample puzzle encoding
        bool init_c_0 = GET_ELEMENT(0, input) == 0x3;
        bool init_c_1 = GET_ELEMENT(1, input) == 0x1;
        bool init_c_2 = GET_ELEMENT(3, input) == 0x2;
        bool init_c_3 = GET_ELEMENT(4, input) == 0x2;
        bool init_c_4 = GET_ELEMENT(5, input) == 0x0;
        bool init_c_5 = GET_ELEMENT(6, input) == 0x3;
        bool init_c_6 = GET_ELEMENT(7, input) == 0x1;
        bool init_c_7 = GET_ELEMENT(10, input) == 0x2;
        bool init_c_8 = GET_ELEMENT(14, input) == 0x1;
        bool init_c_9 = GET_ELEMENT(15, input) == 0x3;
        bool init_total = init_c_0 && init_c_1 && init_c_2 && init_c_3 &&
                init_c_4 && init_c_5 && init_c_6 && init_c_7 && init_c_8 && init_c_9;

        bool row_constr = true, col_constr = true, sq_constr = true;
        for(int k = 0; k < 4; k++){
                // iterate through all columns
                for(int i = 0; i < 4; i++){
                        bool single_row_constr = false, single_col_constr = false,
                                single_sq_constr = false;
                        // iterate through all cells in a column/row
                        for(int j = 0; j < 4; j++){
                                // say that a cell must contain input
                                // note that XOR works here because even if
                                // you have three true, then one of the other
                                // constraints is going to be violated
                                single_sq_constr ^= GET_ELEMENT(((i & 1) * 2)
                                                                + ((i & 2) * 4)
                                                                + ((j == 3) ? 5 : j * j),
                                                                input) == k;
                                single_row_constr ^= GET_ELEMENT(i * 4 + j, input) == k;
                                single_col_constr ^= GET_ELEMENT(i + j * 4, input) == k;
                        }
                        sq_constr &= single_sq_constr;
                        row_constr &= single_row_constr;
                        col_constr &= single_col_constr;
                }
        }

        // if all requirements are satisfiable, perform a null deref
        if(init_total && sq_constr && row_constr && col_constr){
                int * a = NULL;
                printf("Solved the puzzle. %d", *a);
        }
}

int main(int argc,char ** argv) {
        print_board(argc);
        sudoku_solver(argc);
        return 0;
}
