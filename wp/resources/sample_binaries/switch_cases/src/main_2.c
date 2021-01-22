#include <stdlib.h>
#include <stdio.h>

enum comm_t {SURFACE, TEST, RECORD, NAV, DEPLOY};

typedef struct {
  enum comm_t msg_type;
  void *data;
} msg;

void adjust_heading(void *data);

void deploy_payload(void);

void process_message(msg m) {

  switch (m.msg_type) {

  case NAV:
    adjust_heading(m.data);

  case DEPLOY:
    deploy_payload();
    break;

  default:
    break;
  }
}












void adjust_heading(void *data) {}

void deploy_payload(void) {}

int main() {

  msg m;
  process_message(m);

  return 0;
}
