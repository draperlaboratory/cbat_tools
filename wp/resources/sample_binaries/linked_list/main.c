#include <stdlib.h>
#include <stdio.h>

typedef struct ll_node {
  int content;
  struct ll_node *next;
} node;

node* create_linked_list(){
  node* tail = NULL;
  tail->content = 1;
  return tail;
}

int main(int argc, char **argv) {
  create_linked_list(1);
  return 0;
}
