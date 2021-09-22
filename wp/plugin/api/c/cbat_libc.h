#include <stddef.h>
#include "cbat.h"

// Set LIBC_UNROLL to a desired value between 1 and 16. Default is 8.
#ifndef LIBC_UNROLL
#define LIBC_UNROLL 8
#endif

#define strcmp cbat_libc_strcmp
#define strlen cbat_libc_strlen
#define strcpy cbat_libc_strcpy
#define strncpy cbat_libc_strncpy
#define memcmp cbat_libc_memcmp
#define memcpy cbat_libc_memcpy
#define memset cbat_libc_memset

#define UNROLL_EXCEEDED __VERIFIER_assume(false)

int cbat_libc_strcmp(const char* s1, const char* s2) {

#if LIBC_UNROLL >= 1
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL >= 2
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL >= 3
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL >= 4
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL >= 5
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL >= 6
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL >= 7
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL >= 8
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL >= 9
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL >= 10
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL >= 11
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL >= 12
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL >= 13
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL >= 14
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL >= 15
  if (*s1 == 0 || *s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL >= 16
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

#if LIBC_UNROLL >= 1
  if (*s == 0) goto done; len++; s++;
#endif
#if LIBC_UNROLL >= 2
  if (*s == 0) goto done; len++; s++;
#endif
#if LIBC_UNROLL >= 3
  if (*s == 0) goto done; len++; s++;
#endif
#if LIBC_UNROLL >= 4
  if (*s == 0) goto done; len++; s++;
#endif
#if LIBC_UNROLL >= 5
  if (*s == 0) goto done; len++; s++;
#endif
#if LIBC_UNROLL >= 6
  if (*s == 0) goto done; len++; s++;
#endif
#if LIBC_UNROLL >= 7
  if (*s == 0) goto done; len++; s++;
#endif
#if LIBC_UNROLL >= 8
  if (*s == 0) goto done; len++; s++;
#endif
#if LIBC_UNROLL >= 9
  if (*s == 0) goto done; len++; s++;
#endif
#if LIBC_UNROLL >= 10
  if (*s == 0) goto done; len++; s++;
#endif
#if LIBC_UNROLL >= 11
  if (*s == 0) goto done; len++; s++;
#endif
#if LIBC_UNROLL >= 12
  if (*s == 0) goto done; len++; s++;
#endif
#if LIBC_UNROLL >= 13
  if (*s == 0) goto done; len++; s++;
#endif
#if LIBC_UNROLL >= 14
  if (*s == 0) goto done; len++; s++;
#endif
#if LIBC_UNROLL >= 15
  if (*s == 0) goto done; len++; s++;
#endif
#if LIBC_UNROLL >= 16
  if (*s == 0) goto done; len++; s++;
#endif

  UNROLL_EXCEEDED;

 done:
  return len;
}

char * cbat_libc_strcpy(char * dest, const char * src){

  char * ret = dest;

#if LIBC_UNROLL >= 1
  *dest = *src; if (*src == 0) goto done; src++; dest++;
#endif
#if LIBC_UNROLL >= 2
  *dest = *src; if (*src == 0) goto done; src++; dest++;
#endif
#if LIBC_UNROLL >= 3
  *dest = *src; if (*src == 0) goto done; src++; dest++;
#endif
#if LIBC_UNROLL >= 4
  *dest = *src; if (*src == 0) goto done; src++; dest++;
#endif
#if LIBC_UNROLL >= 5
  *dest = *src; if (*src == 0) goto done; src++; dest++;
#endif
#if LIBC_UNROLL >= 6
  *dest = *src; if (*src == 0) goto done; src++; dest++;
#endif
#if LIBC_UNROLL >= 7
  *dest = *src; if (*src == 0) goto done; src++; dest++;
#endif
#if LIBC_UNROLL >= 8
  *dest = *src; if (*src == 0) goto done; src++; dest++;
#endif
#if LIBC_UNROLL >= 9
  *dest = *src; if (*src == 0) goto done; src++; dest++;
#endif
#if LIBC_UNROLL >= 10
  *dest = *src; if (*src == 0) goto done; src++; dest++;
#endif
#if LIBC_UNROLL >= 11
  *dest = *src; if (*src == 0) goto done; src++; dest++;
#endif
#if LIBC_UNROLL >= 12
  *dest = *src; if (*src == 0) goto done; src++; dest++;
#endif
#if LIBC_UNROLL >= 13
  *dest = *src; if (*src == 0) goto done; src++; dest++;
#endif
#if LIBC_UNROLL >= 14
  *dest = *src; if (*src == 0) goto done; src++; dest++;
#endif
#if LIBC_UNROLL >= 15
  *dest = *src; if (*src == 0) goto done; src++; dest++;
#endif
#if LIBC_UNROLL >= 16
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
#if LIBC_UNROLL >= 1
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
#endif
#if LIBC_UNROLL >= 2
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
#endif
#if LIBC_UNROLL >= 3
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
#endif
#if LIBC_UNROLL >= 4
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
#endif
#if LIBC_UNROLL >= 5
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
#endif
#if LIBC_UNROLL >= 6
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
#endif
#if LIBC_UNROLL >= 7
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
#endif
#if LIBC_UNROLL >= 8
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
#endif
#if LIBC_UNROLL >= 9
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
#endif
#if LIBC_UNROLL >= 10
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
#endif
#if LIBC_UNROLL >= 11
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
#endif
#if LIBC_UNROLL >= 12
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
#endif
#if LIBC_UNROLL >= 13
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
#endif
#if LIBC_UNROLL >= 14
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
#endif
#if LIBC_UNROLL >= 15
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
#endif
#if LIBC_UNROLL >= 16
  *dest = *src; copied++; if (copied == n || *src == 0) goto pad_nulls; src++; dest++;
#endif

   pad_nulls:
#if 0
  // Fill remaining bytes with null byte
  dest++;
  int pad_bytes = n - copied;
#if LIBC_UNROLL >= 1
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
#endif
#if LIBC_UNROLL >= 2
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
#endif
#if LIBC_UNROLL >= 3
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
#endif
#if LIBC_UNROLL >= 4
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
#endif
#if LIBC_UNROLL >= 5
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
#endif
#if LIBC_UNROLL >= 6
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
#endif
#if LIBC_UNROLL >= 7
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
#endif
#if LIBC_UNROLL >= 8
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
#endif
#if LIBC_UNROLL >= 9
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
#endif
#if LIBC_UNROLL >= 10
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
#endif
#if LIBC_UNROLL >= 11
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
#endif
#if LIBC_UNROLL >= 12
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
#endif
#if LIBC_UNROLL >= 13
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
#endif
#if LIBC_UNROLL >= 14
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
#endif
#if LIBC_UNROLL >= 15
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
#endif
#if LIBC_UNROLL >= 16
  if (pad_bytes == 0) goto done; *dest = 0; dest++; pad_bytes--;
#endif
  
#endif
  
  UNROLL_EXCEEDED;

 done:
  return ret;
}

int cbat_libc_memcmp(const void *p1, const void *p2, size_t n){

  unsigned char * s1 = (unsigned char *) p1;
  unsigned char * s2 = (unsigned char *) p2;

#if LIBC_UNROLL >= 1
  if (*s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL >= 2
  if (*s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL >= 3
  if (*s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL >= 4
  if (*s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL >= 5
  if (*s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL >= 6
  if (*s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL >= 7
  if (*s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL >= 8
  if (*s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL >= 9
  if (*s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL >= 10
  if (*s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL >= 11
  if (*s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL >= 12
  if (*s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL >= 13
  if (*s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL >= 14
  if (*s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL >= 15
  if (*s1 != *s2) goto done; s1++; s2++;
#endif
#if LIBC_UNROLL >= 16
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

#if LIBC_UNROLL >= 1
  if (copied == n) goto done; *d = *s; copied++; d++; s++;
#endif
#if LIBC_UNROLL >= 2
  if (copied == n) goto done; *d = *s; copied++; d++; s++;
#endif
#if LIBC_UNROLL >= 3
  if (copied == n) goto done; *d = *s; copied++; d++; s++;
#endif
#if LIBC_UNROLL >= 4
  if (copied == n) goto done; *d = *s; copied++; d++; s++;
#endif
#if LIBC_UNROLL >= 5
  if (copied == n) goto done; *d = *s; copied++; d++; s++;
#endif
#if LIBC_UNROLL >= 6
  if (copied == n) goto done; *d = *s; copied++; d++; s++;
#endif
#if LIBC_UNROLL >= 7
  if (copied == n) goto done; *d = *s; copied++; d++; s++;
#endif
#if LIBC_UNROLL >= 8
  if (copied == n) goto done; *d = *s; copied++; d++; s++;
#endif
#if LIBC_UNROLL >= 9
  if (copied == n) goto done; *d = *s; copied++; d++; s++;
#endif
#if LIBC_UNROLL >= 10
  if (copied == n) goto done; *d = *s; copied++; d++; s++;
#endif
#if LIBC_UNROLL >= 11
  if (copied == n) goto done; *d = *s; copied++; d++; s++;
#endif
#if LIBC_UNROLL >= 12
  if (copied == n) goto done; *d = *s; copied++; d++; s++;
#endif
#if LIBC_UNROLL >= 13
  if (copied == n) goto done; *d = *s; copied++; d++; s++;
#endif
#if LIBC_UNROLL >= 14
  if (copied == n) goto done; *d = *s; copied++; d++; s++;
#endif
#if LIBC_UNROLL >= 15
  if (copied == n) goto done; *d = *s; copied++; d++; s++;
#endif
#if LIBC_UNROLL >= 16
  if (copied == n) goto done; *d = *s; copied++; d++; s++;
#endif

  UNROLL_EXCEEDED;
  
 done:
  return dest;
}

void * cbat_libc_memset(void *s, int c, size_t n){

  char * p = (char *) s;
  char byte = (char) c;
  
  if (n > LIBC_UNROLL){
    UNROLL_EXCEEDED;
  }
  
#if LIBC_UNROLL >= 1
  if (n == 0) goto done; *p = byte; n--; p++;
#endif
#if LIBC_UNROLL >= 2
  if (n == 0) goto done; *p = byte; n--; p++;
#endif
#if LIBC_UNROLL >= 3
  if (n == 0) goto done; *p = byte; n--; p++;
#endif
#if LIBC_UNROLL >= 4
  if (n == 0) goto done; *p = byte; n--; p++;
#endif
#if LIBC_UNROLL >= 5
  if (n == 0) goto done; *p = byte; n--; p++;
#endif
#if LIBC_UNROLL >= 6
  if (n == 0) goto done; *p = byte; n--; p++;
#endif
#if LIBC_UNROLL >= 7
  if (n == 0) goto done; *p = byte; n--; p++;
#endif
#if LIBC_UNROLL >= 8
  if (n == 0) goto done; *p = byte; n--; p++;
#endif
#if LIBC_UNROLL >= 9
  if (n == 0) goto done; *p = byte; n--; p++;
#endif
#if LIBC_UNROLL >= 10
  if (n == 0) goto done; *p = byte; n--; p++;
#endif
#if LIBC_UNROLL >= 11
  if (n == 0) goto done; *p = byte; n--; p++;
#endif
#if LIBC_UNROLL >= 12
  if (n == 0) goto done; *p = byte; n--; p++;
#endif
#if LIBC_UNROLL >= 13
  if (n == 0) goto done; *p = byte; n--; p++;
#endif
#if LIBC_UNROLL >= 14
  if (n == 0) goto done; *p = byte; n--; p++;
#endif
#if LIBC_UNROLL >= 15
  if (n == 0) goto done; *p = byte; n--; p++;
#endif
#if LIBC_UNROLL >= 16
  if (n == 0) goto done; *p = byte; n--; p++;
#endif

  UNROLL_EXCEEDED;
  
 done:
  return s;
}
