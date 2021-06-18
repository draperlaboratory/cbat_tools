#include <stdlib.h>
#include <assert.h>
#include <string.h>

struct Account {
  int balance;
} account, account_copy;


int main(int argc,char ** argv) {
  account.balance = 2048;
  memcpy(&account_copy, &account, argc);
  if (account_copy.balance)
    return 0;
  else
    return 1;
}

