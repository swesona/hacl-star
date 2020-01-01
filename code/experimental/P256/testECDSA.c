#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdbool.h>
#include <time.h>

#include "testECDSASignature.c"
#include "testECDSAVerification.c"

#include "ecdsap256-c/Hacl_Impl_ECDSA_P256SHA256_Signature.h"
#include "ecdsap256-c/Hacl_Impl_ECDSA_P256SHA256_Verification.h"

#include <stdio.h>
#include <stdlib.h>

#include <unistd.h>



int main()
{
    testEcdsaSignature0();
    testEcdsaSignature1();
    testEcdsaSignature2();
    testEcdsaSignature3();
    testEcdsaSignature4();
    testEcdsaSignature5();
    testEcdsaSignature6();
    testEcdsaSignature7();
    testEcdsaSignature8();
    testEcdsaSignature9();

    testEcdsaVerification1();
    testEcdsaVerification2();
    testEcdsaVerification3();
    testEcdsaVerification4();
    testEcdsaVerification5();

}