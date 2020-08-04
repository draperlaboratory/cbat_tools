#include <assert.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#pragma GCC push_options
#pragma GCC optimize ("unroll-loops")


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
        for(int i = 0; i < 16; i++){
                if((bb >> i) & 1){
                        return i;
                }
        }

}

// calculate the least significant bit (32bit version)
int rightmost_index_32(uint32_t bb){
        if(bb == 0){
                return  0;
        }
        for(int i = 0; i < 32; i++){
                if((bb >> i) & 1){
                        return i;
                }
        }
}

// calculate the least significant bit (64bit version)
int rightmost_index_64(uint64_t bb){
        if(bb == 0){
                return  0;
        }
#pragma GCC unroll 64
        for(int i = 0; i < 64; i++){
                if((bb >> i) & 1){
                        return i;
                }
        }
}

#define uint128_t __uint128_t
// calculate the least significant bit (64bit version)
int rightmost_index_128(uint128_t bb){
        if(bb == 0){
                return  0;
        }
        bb = ((uint128_t) ((uint64_t) bb));
        for(int i = 0; i < 128; i++){
                if((bb >> i) & 1){
                        return i;
                }
        }
}


int main(int argc,char ** argv) {
	printf("%d\n", rightmost_index_128(0x2));
        return 0;
}
