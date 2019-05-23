#include <stdbool.h>
#include <stdio.h>

typedef enum {NAV, DEPLOY, LOG_STATUS} status_t;

bool process_status(status_t status) {
  bool nav = false;
  bool log = false;
  bool deploy = false;

  switch (status) {
    case NAV:
      nav = true;

    case LOG_STATUS:
      log = true;
      break;

    case DEPLOY:
      deploy = true;
      break;
  }
  return deploy;
}

int main() {

  status_t status = NAV;

  if (process_status(status)) {
    printf("Payload deployed.\n");
  }

  return 0;
}
