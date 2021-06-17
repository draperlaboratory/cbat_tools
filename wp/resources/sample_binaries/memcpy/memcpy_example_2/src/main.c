// To run and collect info:
// clang -O0 -g -o main main.c ; objdump -S main > main.S ; bap wp --func=main --show=bir ./main > main.bir ; grep -r "@memcpy"
// Warning: Changing the optimization flag for this example may cause memcpy to not show up in the bir.

#include <stdlib.h>
#include <assert.h>
#include <string.h>

struct Account {
  int balance;
} account, account_copy;


int main(int argc,char ** argv) {
  //Account* account;
  //Account account_copy;
  account.balance = 2048;
  memcpy(&account_copy, &account, argc);
  if (account_copy.balance)
    return 0;
  else
    return 1;
}

