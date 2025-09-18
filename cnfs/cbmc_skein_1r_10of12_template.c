#include <stdint.h>
#include <limits.h>
#include <stddef.h>

const int WCNT = 8; // WCNT = SKEIN_512_STATE_WORDS

/* key injection*/
#define InjectKey(r)                                                \
    for (i=0;i < WCNT;i++)                                          \
         X[i] += ks[((r)+i) % (WCNT+1)];                            \
    X[WCNT-3] += ts[((r)+0) % 3];                                   \
    X[WCNT-2] += ts[((r)+1) % 3];                                   \
    X[WCNT-1] += (r);

/* 64-bit rotate left */
uint64_t RotL_64(uint64_t x, unsigned int N)
{
    return (x << (N & 63)) | (x >> ((64 - N) & 63));
}

void Skein_Get64_LSB_First(uint64_t *dst, const uint8_t* src, size_t wCnt)
{
    size_t n;

    for (n = 0; n < 8 * wCnt; n += 8)
        dst[n / 8] = (((uint64_t)src[n])) +
        (((uint64_t)src[n + 1]) << 8) +
        (((uint64_t)src[n + 2]) << 16) +
        (((uint64_t)src[n + 3]) << 24) +
        (((uint64_t)src[n + 4]) << 32) +
        (((uint64_t)src[n + 5]) << 40) +
        (((uint64_t)src[n + 6]) << 48) +
        (((uint64_t)src[n + 7]) << 56);
}

int main(int argc, char** argv) {
    uint8_t msgBlkPtr[64]; // message block
    size_t i;
    // size_t r;
    uint64_t X[8];  // chaining variables 
    uint64_t output[8];
    uint64_t ts[3];        /* key schedule: tweak */
    uint64_t ks[WCNT + 1]; /* key schedule: chaining vars */
    uint64_t w[WCNT];      /* local copy of input block */
    unsigned int R_512_0_0 = 46;
    unsigned int R_512_0_1 = 36;
    unsigned int R_512_0_2 = 19;
    unsigned int R_512_0_3 = 37;
    unsigned int R_512_1_0 = 33;
    unsigned int R_512_1_1 = 27;
    unsigned int R_512_1_2 = 14;
    /*
    unsigned int R_512_1_3 = 42;
    unsigned int R_512_2_0 = 17;
    unsigned int R_512_2_1 = 49;
    unsigned int R_512_2_2 = 36;
    unsigned int R_512_2_3 = 39;
    unsigned int R_512_3_0 = 44;
    unsigned int R_512_3_1 = 9;
    unsigned int R_512_3_2 = 54;
    unsigned int R_512_3_3 = 56;
    unsigned int R_512_4_0 = 39;
    unsigned int R_512_4_1 = 30;
    unsigned int R_512_4_2 = 34;
    unsigned int R_512_4_3 = 24;
    unsigned int R_512_5_0 = 13;
    unsigned int R_512_5_1 = 50;
    unsigned int R_512_5_2 = 10;
    unsigned int R_512_5_3 = 17;
    unsigned int R_512_6_0 = 25;
    unsigned int R_512_6_1 = 29;
    unsigned int R_512_6_2 = 39;
    unsigned int R_512_6_3 = 43;
    unsigned int R_512_7_0 = 8;
    unsigned int R_512_7_1 = 35;
    unsigned int R_512_7_2 = 56;
    unsigned int R_512_7_3 = 22;
    */

    // From the documentation, B.8:
    // Skein-512-256
    __CPROVER_assume(X[0] == 0xCCD044A12FDB3E13);
    __CPROVER_assume(X[1] == 0xE83590301A79A9EB);
    __CPROVER_assume(X[2] == 0x55AEA0614F816E6F);
    __CPROVER_assume(X[3] == 0x2A2767A4AE9B94DB);
    __CPROVER_assume(X[4] == 0xEC06025E74DD7683);
    __CPROVER_assume(X[5] == 0xE7A436CDC4746251);
    __CPROVER_assume(X[6] == 0xC36FBAF9393AD185);
    __CPROVER_assume(X[7] == 0x3EEDBA1833EDFC13);

    // Call a compression function on one 512-bit message block

    /* precompute the key schedule for this block */
    ks[WCNT] = 0x1bd11bdaa9fc1a22; // SKEIN_KS_PARITY;
    for (i = 0; i < WCNT; i++)
    {
        ks[i] = X[i];
        ks[WCNT] ^= X[i];            /* compute overall parity */
    }

    // mod: in Skein_512_Init(): Skein_Start_New_Type(ctx,MSG);
    // So before the first message block in Skein_512_Process_Block(),
    // T[0] = 0, T[1] = 8070450532247928832
    // Since here the first message block after it, T[0] = byteCntAdd
    // because of T[0] += byteCntAdd;            /* update processed length */
    // T[0]=byteCntAdd, so T[0]=SKEIN_512_BLOCK_BYTES, so T[0]=64
    // T[1] = SKEIN_T1_FLAG_FIRST | SKEIN_T1_BLK_TYPE_MSG = 8070450532247928832
    ts[0] = 64; //ts[0] = T[0];
    ts[1] = 8070450532247928832; //ts[1] = T[1];
    ts[2] = ts[0] ^ ts[1];

    Skein_Get64_LSB_First(w, msgBlkPtr, WCNT); /* get input block in little-endian format */
    for (i = 0; i < WCNT; i++)               /* do the first full key injection */
    {
        X[i] = w[i] + ks[i];
    }
    X[WCNT - 3] += ts[0];
    X[WCNT - 2] += ts[1];

    /*
    // 9 iterations, 8 rounds each:
    for (r = 1; r <= SKEIN_512_ROUNDS_TOTAL / 8; r++)
    {
        // unroll 8 rounds
        X[0] += X[1]; X[1] = RotL_64(X[1], R_512_0_0); X[1] ^= X[0];
        X[2] += X[3]; X[3] = RotL_64(X[3], R_512_0_1); X[3] ^= X[2];
        X[4] += X[5]; X[5] = RotL_64(X[5], R_512_0_2); X[5] ^= X[4];
        X[6] += X[7]; X[7] = RotL_64(X[7], R_512_0_3); X[7] ^= X[6];
        ...
    }
    */

    // First iteration, so r == 1
    //r = 1;
    // 1st round:
    X[0] += X[1]; X[1] = RotL_64(X[1], R_512_0_0); X[1] ^= X[0];
    X[2] += X[3]; X[3] = RotL_64(X[3], R_512_0_1); X[3] ^= X[2];
    X[4] += X[5]; X[5] = RotL_64(X[5], R_512_0_2); X[5] ^= X[4];
    X[6] += X[7]; X[7] = RotL_64(X[7], R_512_0_3); X[7] ^= X[6];

    // 2nd round:
    X[2] += X[1]; X[1] = RotL_64(X[1], R_512_1_0); X[1] ^= X[2];
    X[4] += X[7]; X[7] = RotL_64(X[7], R_512_1_1); X[7] ^= X[4];
    X[6] += X[5]; X[5] = RotL_64(X[5], R_512_1_2); X[5] ^= X[6];
    X[0] += X[3]; //X[3] = RotL_64(X[3], R_512_1_3); X[3] ^= X[0];
/*
    // 3rd round:
    X[4] += X[1]; X[1] = RotL_64(X[1], R_512_2_0); X[1] ^= X[4];
    X[6] += X[3]; X[3] = RotL_64(X[3], R_512_2_1); X[3] ^= X[6];
    X[0] += X[5]; X[5] = RotL_64(X[5], R_512_2_2); X[5] ^= X[0];
    X[2] += X[7]; X[7] = RotL_64(X[7], R_512_2_3); X[7] ^= X[2];

    // 4th round:
    X[6] += X[1]; X[1] = RotL_64(X[1], R_512_3_0); X[1] ^= X[6];
    X[0] += X[7]; X[7] = RotL_64(X[7], R_512_3_1); X[7] ^= X[0];
    X[2] += X[5]; X[5] = RotL_64(X[5], R_512_3_2); X[5] ^= X[2];
    X[4] += X[3]; X[3] = RotL_64(X[3], R_512_3_3); X[3] ^= X[4];
    InjectKey(2 * r - 1);
    
    // 5th round:
    X[0] += X[1]; X[1] = RotL_64(X[1], R_512_4_0); X[1] ^= X[0];
    X[2] += X[3]; X[3] = RotL_64(X[3], R_512_4_1); X[3] ^= X[2];
    X[4] += X[5]; X[5] = RotL_64(X[5], R_512_4_2); X[5] ^= X[4];
    X[6] += X[7]; X[7] = RotL_64(X[7], R_512_4_3); X[7] ^= X[6];

    // 6th round:
    X[2] += X[1]; X[1] = RotL_64(X[1], R_512_5_0); X[1] ^= X[2];
    X[4] += X[7]; X[7] = RotL_64(X[7], R_512_5_1); X[7] ^= X[4];
    X[6] += X[5]; X[5] = RotL_64(X[5], R_512_5_2); X[5] ^= X[6];
    X[0] += X[3]; X[3] = RotL_64(X[3], R_512_5_3); X[3] ^= X[0];
    
    // 7th round:
    X[4] += X[1]; X[1] = RotL_64(X[1], R_512_6_0); X[1] ^= X[4];
    X[6] += X[3]; X[3] = RotL_64(X[3], R_512_6_1); X[3] ^= X[6];
    X[0] += X[5]; X[5] = RotL_64(X[5], R_512_6_2); X[5] ^= X[0];
    X[2] += X[7]; X[7] = RotL_64(X[7], R_512_6_3); X[7] ^= X[2];
    
    // 8th round:
    X[6] += X[1]; X[1] = RotL_64(X[1], R_512_7_0); X[1] ^= X[6];
    X[0] += X[7]; X[7] = RotL_64(X[7], R_512_7_1); X[7] ^= X[0];
    X[2] += X[5]; X[5] = RotL_64(X[5], R_512_7_2); X[5] ^= X[2];
    X[4] += X[3]; X[3] = RotL_64(X[3], R_512_7_3); X[3] ^= X[4];
    InjectKey(2 * r);
*/
    /* do the final "feedforward" xor, update context chaining vars */
    for (i = 0; i < WCNT; i++)
        output[i] = X[i] ^ w[i];

    //for (i = 0; i < 64; i++)
    //__CPROVER_assume(msgBlkPtr[i] == 0);

    // Output of 1 round given 0-message:
    /*
    __CPROVER_assume(output[0] == 0xb505d4d14a54e7fe);
    __CPROVER_assume(output[1] == 0xdf7f2edc2e58e160);
    __CPROVER_assume(output[2] == 0x7fd60805fe1d034a);
    __CPROVER_assume(output[3] == 0x966f45b75c6b7900);
    __CPROVER_assume(output[4] == 0xd3aa392c3951d914);
    __CPROVER_assume(output[5] == 0x65c41a8f2ddee435);
    __CPROVER_assume(output[6] == 0x725d75116d28cd98);
    __CPROVER_assume(output[7] == 0xfe2f776b09f8e9e);
    */

    __CPROVER_assert(0, "test");
    return 0;
}
