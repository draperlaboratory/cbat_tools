#include <assert.h>

int main(int argc, char** argv) {

    if (argc == 0xdeadbeef) {
        assert(0);
    }

    return 0;

}
