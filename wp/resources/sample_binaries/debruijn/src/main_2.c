#include <assert.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>



// calculate the least significant bit (8bit version)
int rightmost_index_8(uint8_t bb){
        if(bb == 0){
                return 0;
        }
        if((bb >> 0) & 1){
                return 0;
        }
        if((bb >> 1) & 1){
                return 1;
        }
        if((bb >> 2) & 1){
                return 2;
        }
        if((bb >> 3) & 1){
                return 3;
        }
        if((bb >> 4) & 1){
                return 4; }
        if((bb >> 5) & 1){
                return 5;
        }
        if((bb >> 6) & 1){
                return 6;
        }
        if((bb >> 7) & 1){
                return 7;
        }
}

// calculate the least significant bit (16bit version)
int rightmost_index_16(uint16_t bb){
        if(bb == 0){
                return 0;
        }
        if((bb >> 0) & 1){
                return 0;
        }
        if((bb >> 1) & 1){
                return 1;
        }
        if((bb >> 2) & 1){
                return 2;
        }
        if((bb >> 3) & 1){
                return 3;
        }
        if((bb >> 4) & 1){
                return 4;
        }
        if((bb >> 5) & 1){
                return 5;
        }
        if((bb >> 6) & 1){
                return 6;
        }
        if((bb >> 7) & 1){
                return 7;
        }
        if((bb >> 8) & 1){
                return 8;
        }
        if((bb >> 9) & 1){
                return 9;
        }
        if((bb >> 10) & 1){
                return 10;
        }
        if((bb >> 11) & 1){
                return 11;
        }
        if((bb >> 12) & 1){
                return 12;
        }
        if((bb >> 13) & 1){
                return 13;
        }
        if((bb >> 14) & 1){
                return 14;
        }
        if((bb >> 15) & 1){
                return 15;
        }
}

// calculate the least significant bit (32bit version)
int rightmost_index_32(uint32_t bb){
        if(bb == 0){
                return  0;
        }
        if((bb >> 0) & 1){
                return 0;
        }
        if((bb >> 1) & 1){
                return 1;
        }
        if((bb >> 2) & 1){
                return 2;
        }
        if((bb >> 3) & 1){
                return 3;
        }
        if((bb >> 4) & 1){
                return 4;
        }
        if((bb >> 5) & 1){
                return 5;
        }
        if((bb >> 6) & 1){
                return 6;
        }
        if((bb >> 7) & 1){
                return 7;
        }
        if((bb >> 8) & 1){
                return 8;
        }
        if((bb >> 9) & 1){
                return 9;
        }
        if((bb >> 10) & 1){
                return 10;
        }
        if((bb >> 11) & 1){
                return 11;
        }
        if((bb >> 12) & 1){
                return 12;
        }
        if((bb >> 13) & 1){
                return 13;
        }
        if((bb >> 14) & 1){
                return 14;
        }
        if((bb >> 15) & 1){
                return 15;
        }
        if((bb >> 16) & 1){
                return 16;
        }
        if((bb >> 17) & 1){
                return 17;
        }
        if((bb >> 18) & 1){
                return 18;
        }
        if((bb >> 19) & 1){
                return 19;
        }
        if((bb >> 20) & 1){
                return 20;
        }
        if((bb >> 21) & 1){
                return 21;
        }
        if((bb >> 22) & 1){
                return 22;
        }
        if((bb >> 23) & 1){
                return 23;
        }
        if((bb >> 24) & 1){
                return 24;
        }
        if((bb >> 25) & 1){
                return 25;
        }
        if((bb >> 26) & 1){
                return 26;
        }
        if((bb >> 27) & 1){
                return 27;
        }
        if((bb >> 28) & 1){
                return 28;
        }
        if((bb >> 29) & 1){
                return 29;
        }
        if((bb >> 30) & 1){
                return 30;
        }
        if((bb >> 31) & 1){
                return 31;
        }
}

// calculate the least significant bit (64bit version)
int rightmost_index_64(uint64_t bb){
        if(bb == 0){
                return  0;
        }
        if((bb >> 0) & 1){
                return 0;
        }
        if((bb >> 1) & 1){
                return 1;
        }
        if((bb >> 2) & 1){
                return 2;
        }
        if((bb >> 3) & 1){
                return 3;
        }
        if((bb >> 4) & 1){
                return 4;
        }
        if((bb >> 5) & 1){
                return 5;
        }
        if((bb >> 6) & 1){
                return 6;
        }
        if((bb >> 7) & 1){
                return 7;
        }
        if((bb >> 8) & 1){
                return 8;
        }
        if((bb >> 9) & 1){
                return 9;
        }
        if((bb >> 10) & 1){
                return 10;
        }
        if((bb >> 11) & 1){
                return 11;
        }
        if((bb >> 12) & 1){
                return 12;
        }
        if((bb >> 13) & 1){
                return 13;
        }
        if((bb >> 14) & 1){
                return 14;
        }
        if((bb >> 15) & 1){
                return 15;
        }
        if((bb >> 16) & 1){
                return 16;
        }
        if((bb >> 17) & 1){
                return 17;
        }
        if((bb >> 18) & 1){
                return 18;
        }
        if((bb >> 19) & 1){
                return 19;
        }
        if((bb >> 20) & 1){
                return 20;
        }
        if((bb >> 21) & 1){
                return 21;
        }
        if((bb >> 22) & 1){
                return 22;
        }
        if((bb >> 23) & 1){
                return 23;
        }
        if((bb >> 24) & 1){
                return 24;
        }
        if((bb >> 25) & 1){
                return 25;
        }
        if((bb >> 26) & 1){
                return 26;
        }
        if((bb >> 27) & 1){
                return 27;
        }
        if((bb >> 28) & 1){
                return 28;
        }
        if((bb >> 29) & 1){
                return 29;
        }
        if((bb >> 30) & 1){
                return 30;
        }
        if((bb >> 31) & 1){
                return 31;
        }
        if((bb >> 32) & 1){
                return 32;
        }
        if((bb >> 33) & 1){
                return 33;
        }
        if((bb >> 34) & 1){
                return 34;
        }
        if((bb >> 35) & 1){
                return 35;
        }
        if((bb >> 36) & 1){
                return 36;
        }
        if((bb >> 37) & 1){
                return 37;
        }
        if((bb >> 38) & 1){
                return 38;
        }
        if((bb >> 39) & 1){
                return 39;
        }
        if((bb >> 40) & 1){
                return 40;
        }
        if((bb >> 41) & 1){
                return 41;
        }
        if((bb >> 42) & 1){
                return 42;
        }
        if((bb >> 43) & 1){
                return 43;
        }
        if((bb >> 44) & 1){
                return 44;
        }
        if((bb >> 45) & 1){
                return 45;
        }
        if((bb >> 46) & 1){
                return 46;
        }
        if((bb >> 47) & 1){
                return 47;
        }
        if((bb >> 48) & 1){
                return 48;
        }
        if((bb >> 49) & 1){
                return 49;
        }
        if((bb >> 50) & 1){
                return 50;
        }
        if((bb >> 51) & 1){
                return 51;
        }
        if((bb >> 52) & 1){
                return 52;
        }
        if((bb >> 53) & 1){
                return 53;
        }
        if((bb >> 54) & 1){
                return 54;
        }
        if((bb >> 55) & 1){
                return 55;
        }
        if((bb >> 56) & 1){
                return 56;
        }
        if((bb >> 57) & 1){
                return 57;
        }
        if((bb >> 58) & 1){
                return 58;
        }
        if((bb >> 59) & 1){
                return 59;
        }
        if((bb >> 60) & 1){
                return 60;
        }
        if((bb >> 61) & 1){
                return 61;
        }
        if((bb >> 62) & 1){
                return 62;
        }
        if((bb >> 63) & 1){
                return 63;
        }
}


int main(int argc,char ** argv) {
	printf("%d\n", rightmost_index_64(2));
        return 0;
}
