#include <assert.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>

// taken from http://supertech.csail.mit.edu/papers/debruijn.pdf
// and https://www.chessprogramming.org/BitScan#DeBruijnMultiplation

// calculate the least significant bit (8bit version)
int rightmost_index_8(uint8_t bb){
        if(bb == 0){
                return 0;
        }
        // mapping from log_2 n binary string from debruijn sequence to its
        // offset in the debruijn sequence
        int index8[8] = {0, 1, 2, 4, 7, 3, 6, 5};
        // debruijn sequence
        uint8_t debruijn8 = 0x17;
        // get lsb, then leftshift to get a unique 3 bit (log_2 8) sequence in
        // the top 3 bits
        // then rightshift by n - log_2 n = 5 to isolate that unique 3 bit
        // sequence then index into index8 array to get the lsb
        return index8[((uint8_t)((bb & -bb) * debruijn8)) >> 5];
}

// calculate the least significant bit (16bit version)
int rightmost_index_16(uint16_t bb){
        if(bb == 0){
                return 0;
        }
        int index16[16] = {0, 1, 2, 5, 3, 9, 6, 11, 15, 4, 8, 10, 14, 7, 13, 12};
        uint32_t debruijn16 = 0x9af;
        return index16[((uint16_t)((bb & -bb) * debruijn16)) >> 12];
}


// calculate the least significant bit (32bit version)
int rightmost_index_32(uint32_t bb){
        if(bb == 0){
                return  0;
        }
        int index32[32] = {
                0, 1, 28, 2, 29, 14, 24, 3, 30, 22, 20, 15, 25, 17, 4, 8,
                31, 27, 13, 23, 21, 19, 16, 7, 26, 12, 18, 6, 11, 5, 10, 9
        };
        uint32_t debruijn32 = 0x077CB531;
        return index32[((uint32_t)((bb & -bb) * debruijn32)) >> 27];
}

// calculate the least significant bit (64bit version)
int rightmost_index_64( uint64_t bb){
        // must have a bit set, or return 0
        if(bb == 0){
                return  0;
        }
        const int index64[64] = {
                 0,  1, 48,  2, 57, 49, 28,  3,
                 61, 58, 50, 42, 38, 29, 17,  4,
                 62, 55, 59, 36, 53, 51, 43, 22,
                 45, 39, 33, 30, 24, 18, 12,  5,
                 63, 47, 56, 27, 60, 41, 37, 16,
                 54, 35, 52, 21, 44, 32, 23, 11,
                 46, 26, 40, 15, 34, 20, 31, 10,
                 25, 14, 19,  9, 13,  8,  7,  6
        };

        uint64_t debruijn64 = 0x03f79d71b4cb0a89;

        return index64[((bb & -bb) * debruijn64) >> 58];
}

// sample invocation
int main(int argc,char ** argv) {
        return 0;
}
