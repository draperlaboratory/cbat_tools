#include <stddef.h>
#include "cbat.h"

// Set LIBC_UNROLL to 4, 8, 12 or 16. Default is 12.
#ifndef LIBC_UNROLL
#define LIBC_UNROLL 12
#endif

#define strcmp cbat_libc_strcmp
#define strlen cbat_libc_strlen
#define strcpy cbat_libc_strcpy
#define strncpy cbat_libc_strncpy
#define memcmp cbat_libc_memcmp
#define memcpy cbat_libc_memcpy

#define UNROLL_EXCEEDED __VERIFIER_assume(true)

int cbat_libc_strcmp(const char* s1, const char* s2) {
  
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
#if LIBC_UNROLL > 4
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL > 8
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL > 12
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
#endif

  UNROLL_EXCEEDED;
  
 done:
  if (*s1 == *s2) return 0;
  if (*s1 > *s2)
    return 1;
  return -1;
}

size_t cbat_libc_strlen(const char* s) {
  
  size_t len = 0;
  if (*s == 0) goto done; len++; s++;
  if (*s == 0) goto done; len++; s++;
  if (*s == 0) goto done; len++; s++;
  if (*s == 0) goto done; len++; s++;
#if LIBC_UNROLL > 4
  if (*s == 0) goto done; len++; s++;
  if (*s == 0) goto done; len++; s++;
  if (*s == 0) goto done; len++; s++;
  if (*s == 0) goto done; len++; s++;
#endif
#if LIBC_UNROLL > 8
  if (*s == 0) goto done; len++; s++;
  if (*s == 0) goto done; len++; s++;
  if (*s == 0) goto done; len++; s++;
  if (*s == 0) goto done; len++; s++;
#endif
#if LIBC_UNROLL > 12
  if (*s == 0) goto done; len++; s++;
  if (*s == 0) goto done; len++; s++;
  if (*s == 0) goto done; len++; s++;
  if (*s == 0) goto done; len++; s++;
#endif

  UNROLL_EXCEEDED;

 done:
  return len;
}

char * cbat_libc_strcpy(char * dest, const char * src){

  char * ret = dest;

  *dest = *src; if (*src == 0) goto done; src++; dest++;
  *dest = *src; if (*src == 0) goto done; src++; dest++;
  *dest = *src; if (*src == 0) goto done; src++; dest++;
  *dest = *src; if (*src == 0) goto done; src++; dest++;
#if LIBC_UNROLL > 4
  *dest = *src; if (*src == 0) goto done; src++; dest++;
  *dest = *src; if (*src == 0) goto done; src++; dest++;
  *dest = *src; if (*src == 0) goto done; src++; dest++;
  *dest = *src; if (*src == 0) goto done; src++; dest++;
#endif
#if LIBC_UNROLL > 8
  *dest = *src; if (*src == 0) goto done; src++; dest++;
  *dest = *src; if (*src == 0) goto done; src++; dest++;
  *dest = *src; if (*src == 0) goto done; src++; dest++;
  *dest = *src; if (*src == 0) goto done; src++; dest++;
#endif
#if LIBC_UNROLL > 12
  *dest = *src; if (*src == 0) goto done; src++; dest++;
  *dest = *src; if (*src == 0) goto done; src++; dest++;
  *dest = *src; if (*src == 0) goto done; src++; dest++;
  *dest = *src; if (*src == 0) goto done; src++; dest++;
#endif

  UNROLL_EXCEEDED;
  
 done:
  return ret;
}

// Note that strncpy *always* copies n bytes: after copying str, it fills with null bytes.
char * cbat_libc_strncpy(char * dest, const char * src, size_t n){

  // Cannot copy more than the unroll factor
  if (n > LIBC_UNROLL){
    UNROLL_EXCEEDED;
  }
  
  char * ret = dest;

  // Copy up to n bytes into dest
  size_t copied = 0;
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
#if LIBC_UNROLL >  4
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
#endif
#if LIBC_UNROLL > 8
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
#endif
#if LIBC_UNROLL > 12
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
#endif  

  // Fill remaining bytes with null byte
 pad_nulls:
  dest++;
  int pad_bytes = n - copied;
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
#if LIBC_UNROLL >  4
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
#endif
#if LIBC_UNROLL > 8
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
#endif
#if LIBC_UNROLL > 12
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
#endif  

  UNROLL_EXCEEDED;

 done:
  return ret;
}

int cbat_libc_memcmp(const void *p1, const void *p2, size_t n){

  unsigned char * s1 = (unsigned char *) p1;
  unsigned char * s2 = (unsigned char *) p2;
  
  if (*s1 != *s2) goto done; s1++; s2++;
  if (*s1 != *s2) goto done; s1++; s2++;
  if (*s1 != *s2) goto done; s1++; s2++;
  if (*s1 != *s2) goto done; s1++; s2++;
#if LIBC_UNROLL > 4
  if (*s1 != *s2) goto done; s1++; s2++;
  if (*s1 != *s2) goto done; s1++; s2++;
  if (*s1 != *s2) goto done; s1++; s2++;
  if (*s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL > 8
  if (*s1 != *s2) goto done; s1++; s2++;
  if (*s1 != *s2) goto done; s1++; s2++;
  if (*s1 != *s2) goto done; s1++; s2++;
  if (*s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL > 12
  if (*s1 != *s2) goto done; s1++; s2++;
  if (*s1 != *s2) goto done; s1++; s2++;
  if (*s1 != *s2) goto done; s1++; s2++;
  if (*s1 != *s2) goto done; s1++; s2++;
#endif

  UNROLL_EXCEEDED;

 done:
  return *s1 - *s2;

}

void * cbat_libc_memcpy(void *dest, const void *src, size_t n){
  unsigned char * d = (unsigned char *) dest;
  const unsigned char * s = (const unsigned char *) src;

  size_t copied = 0;
  if (copied == n) goto done; *d = *s; copied++; d++; s++;
  if (copied == n) goto done; *d = *s; copied++; d++; s++;
  if (copied == n) goto done; *d = *s; copied++; d++; s++;
  if (copied == n) goto done; *d = *s; copied++; d++; s++;  
#if LIBC_UNROLL > 4
  if (copied == n) goto done; *d = *s; copied++; d++; s++;
  if (copied == n) goto done; *d = *s; copied++; d++; s++;
  if (copied == n) goto done; *d = *s; copied++; d++; s++;
  if (copied == n) goto done; *d = *s; copied++; d++; s++;  
#endif
#if LIBC_UNROLL > 8
  if (copied == n) goto done; *d = *s; copied++; d++; s++;
  if (copied == n) goto done; *d = *s; copied++; d++; s++;
  if (copied == n) goto done; *d = *s; copied++; d++; s++;
  if (copied == n) goto done; *d = *s; copied++; d++; s++;  
#endif
#if LIBC_UNROLL > 12
  if (copied == n) goto done; *d = *s; copied++; d++; s++;
  if (copied == n) goto done; *d = *s; copied++; d++; s++;
  if (copied == n) goto done; *d = *s; copied++; d++; s++;
  if (copied == n) goto done; *d = *s; copied++; d++; s++;  
#endif

  UNROLL_EXCEEDED;
  
 done:
  return dest;
}
