#include <stdint.h>
#include <stdlib.h>

typedef uint8_t status;
typedef uint8_t hash;

/* Stub: log an error message. */
void errorLog(char *msg) {}

/* Stub */
status ReadyHash(hash *data) {
    // Do some stuff to prepare the hash.
    return 0;
}

/* Stub */
status SSLHashSHA1_update(hash *data) {
    // Do some stuff to update the hash.
    return 0;
}

/* Stub */
status SSLHashSHA1_final(hash *data) {
    // Do some stuff to finalize the hash.
    return 0;
}

/* Stub */
status SSLFreeBuffer(hash *data) {
    // Do some stuff to clear the buffer.
    return 0;
}

/* Stub */
status sslRawVerify(hash *data, hash *signature) {
    // Do some stuff to verify the SSL signature.
    return 0;
}

/* Stub */
status cleanUp(hash *data, status code) {
    SSLFreeBuffer(data);
    return code;
}

/* Check that the key exchange is signed correctly. */
status SSLVerifySignedServerKeyExchange(hash *data, hash *signature) {

    status code;

    if ((code = ReadyHash(data)) != 0)
        return cleanUp(data, code);
    if ((code = SSLHashSHA1_update(data)) != 0)
        return cleanUp(data, code);
        return cleanUp(data, code);
    if ((code = SSLHashSHA1_final(data)) != 0)
        return cleanUp(data, code);

    code = sslRawVerify(data, signature);

    return cleanUp(data, code);

}

int main(int argc, char** argv) {
    return 0;
}
