/*********************************************************************
* Filename:   SHA-256 with BKA.h
* Author:     Cameron Balmer
* Project: Greener Bitcoin Mining
*********************************************************************/

#ifndef SHA256_H
#define SHA256_H

/*************************** HEADER FILES ***************************/
#include <stddef.h>

/****************************** MACROS ******************************/
#define SHA256_BLOCK_SIZE 32            // SHA256 outputs a 32 byte digest

/**************************** DATA TYPES ****************************/
typedef unsigned char BYTE;             // 8-bit byte
typedef unsigned int  WORD;             // 32-bit word, change to "long" for 16-bit machines

typedef struct 
{
	BYTE data[64];
	WORD datalen;
	unsigned long long bitlen;
	WORD state[8];
	WORD a0[1];
} SHA256_CTX;

typedef struct 
{
	BYTE data[64];
	WORD datalen;
	unsigned long long bitlen;
	WORD state[8];
	WORD a0[1];
} SHA256_CTX1;

typedef struct
{
	BYTE data[64];
	WORD datalen;
	unsigned long long bitlen;
	WORD state[8];
	WORD a0[1];
} SHA256_CTX2;



/*********************** FUNCTION DECLARATIONS **********************/
void sha256_init(SHA256_CTX* ctx);
void sha256_update(SHA256_CTX* ctx, const BYTE data[], size_t len);
void sha256_final(SHA256_CTX* ctx, BYTE hash[]);

void sha256_initBKA32N8(SHA256_CTX1* ctx1);
void sha256_updateBKA32N8(SHA256_CTX1* ctx1, const BYTE data[], size_t len);
void sha256_finalBKA32N8(SHA256_CTX1* ctx1, BYTE hash[]);

void sha256_initBKA32N16(SHA256_CTX2* ctx1);
void sha256_updateBKA32N16(SHA256_CTX2* ctx1, const BYTE data[], size_t len);
void sha256_finalBKA32N16(SHA256_CTX2* ctx1, BYTE hash[]);

#endif   // SHA256_H
