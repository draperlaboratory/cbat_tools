#include <assert.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

// sdbm hash; used in berkeley db
// from http://www.cse.yorku.ca/~oz/hash.html
unsigned long bad_hash(unsigned char str, unsigned long cur_hash);
unsigned long bad_hash(unsigned char str, unsigned long cur_hash){
  return str + (cur_hash << 6) + (cur_hash << 16) - cur_hash;
}

void perform_hash(uint8_t a, uint8_t b, uint8_t c, uint8_t d, uint8_t e);
void perform_hash(uint8_t a, uint8_t b, uint8_t c, uint8_t d, uint8_t e){

  // a hashtable with one special element (captial X)
  const char table[32] =
    {'x', 'x', 'x', 'x', 'x', 'x', 'x', 'x', 'x', 'x', 'x', 'x',
     'x', 'x', 'x', 'X', 'x', 'x', 'x', 'x', 'x', 'x', 'x', 'x',
     'x', 'x', 'x', 'x', 'x', 'x', 'x', 'x', };


  // calculate the hash using sdbm
  unsigned long cur_hash = 0;
  cur_hash = bad_hash(a, cur_hash);
  cur_hash = bad_hash(b, cur_hash);
  cur_hash = bad_hash(c, cur_hash);
  cur_hash = bad_hash(d, cur_hash);
  cur_hash = bad_hash(e, cur_hash);

  // only segfault if the hashed input gets `X` out of the table
  if(table[cur_hash % 32] == 'X'){
    assert(0);
  }
}


// breaking input
int main(int argc, char** argv){
  perform_hash(0x0,0x0,0x0,0x0,0x0);
}
