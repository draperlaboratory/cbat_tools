typedef enum { false, true } bool;
typedef long int loff_t;
typedef char *pchar;
typedef void *pointer;
typedef unsigned long int pthread_t;
typedef unsigned long int sector_t;
typedef long unsigned int size_t;
typedef unsigned int u32;

extern void abort(void)
__attribute__ ((__nothrow__, __leaf__))
__attribute__ ((__noreturn__));

void __attribute__ ((noinline))
__VERIFIER_error(void)
{
  abort();
}

void __attribute__ ((noinline))
__VERIFIER_assume(int expression)
{
  if(!expression) {
    while(1) {
    }
  }
  return;
}

bool __attribute__ ((noinline))
__VERIFIER_nondet_bool(void)
{
  bool val;
  return val;
}

char __attribute__ ((noinline))
__VERIFIER_nondet_char(void)
{
  char val;
  return val;
}

int __attribute__ ((noinline))
__VERIFIER_nondet_int(void)
{
  int val;
  return val;
}

float __attribute__ ((noinline))
__VERIFIER_nondet_float(void)
{
  float val;
  return val;
}

double __attribute__ ((noinline))
__VERIFIER_nondet_double(void)
{
  double val;
  return val;
}

loff_t __attribute__ ((noinline))
__VERIFIER_nondet_loff_t(void)
{
  loff_t val;
  return val;
}

long __attribute__ ((noinline))
__VERIFIER_nondet_long(void)
{
  long val;
  return val;
}

pchar __attribute__ ((noinline))
__VERIFIER_nondet_pchar(void)
{
  pchar val;
  return val;
}

pointer __attribute__ ((noinline))
__VERIFIER_nondet_pointer(void)
{
  pointer val;
  return val;
}

pthread_t __attribute__ ((noinline))
__VERIFIER_nondet_pthread_t(void)
{
  pthread_t val;
  return val;
}

sector_t __attribute__ ((noinline))
__VERIFIER_nondet_sector_t(void)
{
  sector_t val;
  return val;
}

short __attribute__ ((noinline))
__VERIFIER_nondet_short(void)
{
  short val;
  return val;
}

size_t __attribute__ ((noinline))
__VERIFIER_nondet_size_t(void)
{
  size_t val;
  return val;
}

u32 __attribute__ ((noinline))
__VERIFIER_nondet_u32(void)
{
  u32 val;
  return val;
}

unsigned char __attribute__ ((noinline))
__VERIFIER_nondet_uchar(void)
{
  unsigned char val;
  return val;
}

unsigned int __attribute__ ((noinline))
__VERIFIER_nondet_uint(void)
{
  unsigned int val;
  return val;
}

unsigned long __attribute__ ((noinline))
__VERIFIER_nondet_ulong(void)
{
  unsigned long val;
  return val;
}

unsigned __attribute__ ((noinline))
__VERIFIER_nondet_unsigned(void)
{
  unsigned val;
  return val;
}

unsigned short __attribute__ ((noinline))
__VERIFIER_nondet_ushort(void)
{
  unsigned short val;
  return val;
}
