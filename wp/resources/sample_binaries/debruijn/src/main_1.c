#include <assert.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>

// taken from http://supertech.csail.mit.edu/papers/debruijn.pdf
// and https://www.chessprogramming.org/BitScan#DeBruijnMultiplation

// this works because (bb & -bb) isolates the LSB
// debruijn64 bit sequence contains all unique ceil(lg 8)=3 bit binary strings
// left shifting by lsb guarantees unique 3 bit binary string that you can then
// use to index into hash table


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
        int index32[32] =
        {
                0, 1, 28, 2, 29, 14, 24, 3, 30, 22, 20, 15, 25, 17, 4, 8,
                31, 27, 13, 23, 21, 19, 16, 7, 26, 12, 18, 6, 11, 5, 10, 9
        };
        uint32_t debruijn32 = 0x077CB531;
        return index32[((uint32_t)((bb & -bb) * debruijn32)) >> 27];
}

// sample invocation
int main(int argc,char ** argv) {
        return 0;
}
