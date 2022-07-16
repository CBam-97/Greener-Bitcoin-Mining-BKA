/*********************************************************************
* Filename:   SHA-256 with BKA.cpp
* Author:     Stanley Foo
* Project: Greener Bitcoin Mining
*********************************************************************
* Edited by: Cameron Balmer
* Accessed via public GitHub Repository: https://github.com/sfoo03/SHA256withBKA32 on 24/05/2022
* Project: "Greener" Bitcoin Mining using Approximate Computing
*************************** HEADER FILES ***************************/
#include <process.h> 
#include <time.h>
#include <stdlib.h>
#include <stdio.h>
#include <memory.h>
#include <string.h>
#include "SHA-256 with BKA.h"
#include <string>
#include <inttypes.h>
#include <iostream>
#include <fstream>
#include <bitset>
using namespace std;

/****************************** MACROS ******************************/
#define ROTLEFT(a,b) (((a) << (b)) | ((a) >> (32-(b))))
#define ROTRIGHT(a,b) (((a) >> (b)) | ((a) << (32-(b))))

#define CH(x,y,z) (((x) & (y)) ^ (~(x) & (z)))
#define MAJ(x,y,z) (((x) & (y)) ^ ((x) & (z)) ^ ((y) & (z)))
#define EP0(x) (ROTRIGHT(x,2) ^ ROTRIGHT(x,13) ^ ROTRIGHT(x,22))
#define EP1(x) (ROTRIGHT(x,6) ^ ROTRIGHT(x,11) ^ ROTRIGHT(x,25))
#define SIG0(x) (ROTRIGHT(x,7) ^ ROTRIGHT(x,18) ^ ((x) >> 3))
#define SIG1(x) (ROTRIGHT(x,17) ^ ROTRIGHT(x,19) ^ ((x) >> 10))

/**************************** VARIABLES *****************************/
static const WORD k[64] = {
	0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
	0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
	0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
	0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
	0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
	0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
	0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
	0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
};
/*********************** FUNCTION DEFINITIONS ***********************/
// Carry save adders used in SHA256
WORD CSAsum(WORD A, WORD B, WORD C_In)
{
	WORD Sum;
	// Calculating value of sum
	Sum = C_In ^ (A ^ B);
	return Sum;
}
WORD CSAcout(WORD A, WORD B, WORD C_In)
{
	WORD C_Out;
	//Calculating value of C-Out
	C_Out = (A & B) | (B & C_In) | (A & C_In);
	C_Out = (C_Out << 1);
	return C_Out;

}

//BKA32 Functions

#pragma region Original BKA32 Function
// Original BKA32 function
WORD BKA32(WORD n, WORD m) // range -4294967296 to 4294967296 each number
{
	//Code for approximate Brent-Kung adder with K=16 function
	//BKA output
	WORD out;
	WORD sum[32];

	int i, ii, u = 0;
	WORD a[33] = { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 }, b[33] = { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 };
	WORD cin = 0, cout;
	WORD C[33];

	WORD P1[32], P2[16], P3[8], P4[4], P5[2], P6;
	WORD G1[32], G2[16], G3[8], G4[4], G5[2], G6;

	WORD appsum[32], appcout;

	// convert a to binary
	for (i = 0; n > 0; i++)
	{
		a[i] = n % 2;
		n = n / 2;
	}
	// convert b to binary
	for (ii = 0; m > 0; ii++)
	{
		b[ii] = m % 2;
		m = m / 2;
	}

	//^ is bitwise XOR
	// & is bitwise AND
	// | is bitwise OR
	// 

	//Pre-processing stage ---------------------
	//Generate 1st order P's and G's
	C[0] = cin;
	int l = 0;
	for (l = 0; l <= 31; l = l + 1)
	{
		//Propagate
		P1[l] = a[l] ^ b[l]; //pi = ai + bi,
		//Generate
		G1[l] = a[l] & b[l]; // gi = ai .bi
	}
	//------------------------------------------

	//Garry Generation Network -----------------
	//Generate 2nd order P's and G's // all 2 bit values
	int len;
	for (len = 0; len <= 15; len = len + 1)
	{
		P2[len] = P1[2 * len + 1] & P1[2 * len];
		G2[len] = G1[2 * len + 1] | (P1[2 * len + 1] & G1[2 * len]);
	}

	//Generate 3rd order P's and G's //all 4 bit values
	for (len = 0; len <= 7; len = len + 1)
	{
		P3[len] = P2[2 * len + 1] & P2[2 * len];
		G3[len] = G2[2 * len + 1] | (P2[2 * len + 1] & G2[2 * len]);
	}

	//Generate 4th order P's and G's //all 8 bit values?
	for (len = 0; len <= 3; len = len + 1)
	{
		P4[len] = P3[2 * len + 1] & P3[2 * len];
		G4[len] = G3[2 * len + 1] | (P3[2 * len + 1] & G3[2 * len]);
	}

	//Generate 5th order P's and G's //all 16 bit values?
	for (len = 0; len <= 1; len = len + 1)
	{
		P5[len] = P4[2 * len + 1] & P4[2 * len];
		G5[len] = G4[2 * len + 1] | (P4[2 * len + 1] & G4[2 * len]);
	}

	//Generate 6th order P's and G's //all 32 bit values?
	P6 = P5[2 * len + 1] & P5[2 * len];
	G6 = G5[2 * len + 1] | (P5[2 * len + 1] & G5[2 * len]);
	//--------------------------------------------

	//Post Processing Stage ----------------------
	//Generate all carry signals that can be calculated directly from input
	C[1] = G1[0] | (P1[0] & C[0]);
	C[2] = G2[0] | (P2[0] & C[0]);
	C[4] = G3[0] | (P3[0] & C[0]);
	C[8] = G4[0] | (P4[0] & C[0]);
	C[16] = G5[0] | (P5[0] & C[0]);
	C[32] = G6 | (P6 & C[0]); 
	//these are fine

	//Now generating remaining carries
	C[3] = G1[2] | (P1[2] & C[2]); //Ci+i = gi + Pi * Ci
	C[5] = G1[4] | (P1[4] & C[4]);
	C[6] = G2[2] | (P2[2] & C[4]);
	C[7] = G1[6] | (P1[6] & C[6]);

	C[9] = G1[8] | (P1[8] & C[8]);
	C[10] = G2[4] | (P2[4] & C[8]);
	C[11] = G1[10] | (P1[10] & C[10]);
	C[12] = G3[2] | (P3[2] & C[8]);
	C[13] = G1[12] | (P1[12] & C[12]);
	C[14] = G2[6] | (P2[6] & C[12]);

	C[15] = G1[14] | (P1[14] & C[14]);
	C[17] = G1[16] | (P1[16] & C[16]);
	C[18] = G2[8] | (P2[8] & C[16]); //2nd order => /2
	C[19] = G1[18] | (P1[18] & C[18]);
	C[20] = G3[4] | (P3[4] & C[16]); //3rd order = /4

	C[21] = G1[20] | (P1[20] & C[20]);
	C[22] = G2[10] | (P2[10] & C[20]);
	C[23] = G1[22] | (P1[22] & C[22]);
	C[24] = G3[5] | (P3[5] & C[20]); //4th order => /8
	C[25] = G1[24] | (P1[24] & C[24]);
	C[26] = G2[12] | (P2[12] & C[24]);
	C[28] = G3[6] | (P3[6] & C[24]);

	C[27] = G1[26] | (P1[26] & C[26]);
	C[29] = G1[28] | (P1[28] & C[28]);
	C[30] = G2[14] | (P2[14] & C[28]);
	C[31] = G1[30] | (P1[30] & C[30]);

	for (i = 0; i <= 31; i = i + 1)
	{
		sum[i] = P1[i] ^ C[i]; //sum bits of the adder
	}
	//--------------------------------------------
	cout = C[32];

	WORD c[] = { cout, sum[31], sum[30], sum[29], sum[28], sum[27], sum[26], sum[25], sum[24], sum[23], sum[22], sum[21], sum[20], sum[19], sum[18], sum[17], sum[16], sum[15], sum[14], sum[13], sum[12], sum[11], sum[10], sum[9], sum[8], sum[7], sum[6], sum[5], sum[4], sum[3], sum[2], sum[1], sum[0] };
	//WORD c[] = { S[0], S[1], S[2], S[3], S[4], S[5], S[6], S[7], S[8], S[9], S[10], S[11], S[12], S[13], S[14], S[15], S[16], S[17], S[18], S[19], S[20], S[21], S[22], S[23], S[24], S[25], S[26], S[27], S[28], S[29], S[30], S[31], cout };
	//printf("Binary number = %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d \n", cout, S[31], S[30], S[29], S[28], S[27], S[26], S[25], S[24], S[23], S[22], S[21], S[20], S[19], S[18], S[17], S[16], S[15], S[14], S[13], S[12], S[11], S[10], S[9], S[8], S[7], S[6], S[5], S[4], S[3], S[2], S[1], S[0]);

	// convert back to decimal
	int length = sizeof(c) / sizeof(c[0]);
	for (i = 0; i < length; i++)
	{
		if (c[i] == 0)
		{
			u = u * 2;
		}
		else if (c[i] == 1)
		{
			u = u * 2;
			u = u + 1;
		}
		else
		{
			u = u * 2;
		}
	}

	//Calculating value of C-Out
	out = u;
	return out;

}
#pragma endregion

#pragma region BKA32 with K = 8 function
// Approximate BKA32 with K = 8 function
WORD BKA32N8(WORD n, WORD m) // range -4294967296 to 4294967296 each number
{
	//Code for non-approximate Brent-Kung adder, adapted from verilog: https://github.com/Anvesh98/Brentkung-Adder/blob/main/bentkung.v
	//BKA output
	WORD out;
	WORD S[32];

	int i, ii, u = 0;
	WORD a[33] = { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 }, b[33] = { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 };
	WORD cin = 0, cout;
	WORD C[33];

	WORD P1[32], P2[16], P3[8], P4[4];
	WORD G1[32], G2[16], G3[8], G4[4];

	// convert a to binary
	for (i = 0; n > 0; i++)
	{
		a[i] = n % 2;
		n = n / 2;
	}
	// convert b to binary
	for (ii = 0; m > 0; ii++)
	{
		b[ii] = m % 2;
		m = m / 2;
	}

	//^ is bitwise XOR
	// & is bitwise AND
	// | is bitwise OR
	// 

	//Pre-processing stage ---------------------
	//Generate 1st order P's and G's
	C[0] = cin;
	int l = 0;
	for (l = 0; l <= 31; l = l + 1)
	{
		P1[l] = a[l] ^ b[l];
		G1[l] = a[l] & b[l];
	}
	//------------------------------------------

	//Garry Generation Network -----------------
	//Generate 2nd order P's and G's //2nd row
	int len;
	for (len = 0; len <= 15; len = len + 1) // all 2 bit values
	{
		P2[len] = P1[2 * len + 1] & P1[2 * len];
		G2[len] = G1[2 * len + 1] | (P1[2 * len + 1] & G1[2 * len]);
	}

	//Generate 3rd order P's and G's //3rd row
	for (len = 0; len <= 7; len = len + 1) // all 4 bit values
	{
		P3[len] = P2[2 * len + 1] & P2[2 * len];
		G3[len] = G2[2 * len + 1] | (P2[2 * len + 1] & G2[2 * len]);
	}

	//Generate 4th order P's and G's //4th row
	for (len = 0; len <= 3; len = len + 1) // all 8 bit values
	{
		P4[len] = P3[2 * len + 1] & P3[2 * len];
		G4[len] = G3[2 * len + 1] | (P3[2 * len + 1] & G3[2 * len]);
	}

	//Post Processing Stage --------------------
	//Generate all carry signals that can be calculated directly from input
	C[1] = G1[0] | (P1[0] & C[0]);
	C[2] = G2[0] | (P2[0] & C[0]);
	C[4] = G3[0] | (P3[0] & C[0]);

	//Now generating remaining carries
	C[3] = G1[2] | (P1[2] & C[2]); 
	C[5] = G1[4] | (P1[4] & C[4]); 
	C[6] = G2[2] | (P2[2] & C[4]); 
	C[7] = G1[6] | (P1[6] & C[6]); 
	C[8] = G4[0] | (P4[0] & C[4]); 
	C[9] = G1[8] | (P1[8] & C[8]); 
	C[10] = G2[4] | (P2[4] & C[8]); 
	C[11] = G1[10] | (P1[10] & C[10]);
	C[12] = G3[2] | (P3[2] & C[8]); 
	C[13] = G1[12] | (P1[12] & C[12]); 
	C[14] = G2[6] | (P2[6] & C[12]);
	C[15] = G1[14] | (P1[14] & C[14]);

	C[16] = G4[1] | (P4[1] & C[0]);  //Root Carry 16
	C[17] = G1[16] | (P1[16] & C[16]);
	C[18] = G2[8] | (P2[8] & C[16]);
	C[19] = G1[18] | (P1[18] & C[18]);
	C[20] = G3[4] | (P3[4] & C[16]);
	C[21] = G1[20] | (P1[20] & C[20]);
	C[22] = G2[10] | (P2[10] & C[20]);
	C[23] = G1[22] | (P1[22] & C[22]);

	C[24] = G4[2] | (P4[2] & C[0]); //Root Carry 24 
	C[25] = G1[24] | (P1[24] & C[24]);
	C[26] = G2[12] | (P2[12] & C[24]);
	C[27] = G1[26] | (P1[26] & C[26]);
	C[28] = G3[6] | (P3[6] & C[24]);
	C[29] = G1[28] | (P1[28] & C[28]);
	C[30] = G2[14] | (P2[14] & C[28]);
	C[31] = G1[30] | (P1[30] & C[30]);

	C[32] = G4[3] | (P4[3] & C[25]);

	//SMALLER TREE in https://ieeexplore.ieee.org/stamp/stamp.jsp?tp=&arnumber=7508416

	////Post Processing Stage --------------------
	////Generate all carry signals that can be calculated directly from input
	//C[1] = G1[0] | (P1[0] & C[0]);
	//C[2] = G2[0] | (P2[0] & C[0]);
	//C[4] = G3[0] | (P3[0] & C[0]);

	////Now generating remaining carries
	//C[3] = G1[2] | (P1[2] & C[2]);
	//C[5] = G1[4] | (P1[4] & C[4]);
	//C[6] = G2[2] | (P2[2] & C[4]);
	//C[7] = G1[6] | (P1[6] & C[6]);

	//C[8] = G3[1] | (P3[1] & C[0]); // Root Carry 8
	//C[9] = G1[8] | (P1[8] & C[8]);
	//C[10] = G2[4] | (P2[4] & C[8]);
	//C[11] = G1[10] | (P1[10] & C[10]);
	//C[12] = G3[2] | (P3[2] & C[8]); // Root Carry 12
	//C[13] = G1[12] | (P1[12] & C[12]);
	//C[14] = G2[6] | (P2[6] & C[12]);
	//C[15] = G1[14] | (P1[14] & C[14]);

	//C[16] = G3[3] | (P3[3] & C[0]); // Root Carry 16
	//C[17] = G1[16] | (P1[16] & C[16]);
	//C[18] = G2[8] | (P2[8] & C[16]);
	//C[19] = G1[18] | (P1[18] & C[18]);
	//C[20] = G3[4] | (P3[4] & C[16]); // Root Carry 20
	//C[21] = G1[20] | (P1[20] & C[20]);
	//C[22] = G2[10] | (P2[10] & C[20]);
	//C[23] = G1[22] | (P1[22] & C[22]); 

	//C[24] = G3[5] | (P3[5] & C[0]); // Root Carry 24
	//C[25] = G1[24] | (P1[24] & C[24]);
	//C[26] = G2[12] | (P2[12] & C[24]);
	//C[27] = G1[26] | (P1[26] & C[26]);
	//C[28] = G3[6] | (P3[6] & C[24]); // Root Carry 28
	//C[29] = G1[28] | (P1[28] & C[28]); 
	//C[30] = G2[14] | (P2[14] & C[28]); 
	//C[31] = G1[30] | (P1[30] & C[30]); 

	//C[32] = G3[7] | (P3[7] & C[29]);

	////Post Processing Stage --------------------
	////Generate all carry signals that can be calculated directly from input
	//C[1] = G1[0] | (P1[0] & C[0]);
	//C[2] = G2[0] | (P2[0] & C[0]);
	//C[4] = G3[0] | (P3[0] & C[0]);

	////Now generating remaining carries
	//C[3] = G1[2] | (P1[2] & C[2]);

	//C[5] = G1[4] | (P1[4] & C[4]);
	//C[6] = G2[2] | (P2[2] & C[4]);
	//C[7] = G1[6] | (P1[6] & C[6]);
	//C[8] = G3[1] | (P3[1] & C[6]);

	//C[9] = G1[8] | (P1[8] & C[8]);
	//C[10] = G2[4] | (P2[4] & C[8]);
	//C[11] = G1[10] | (P1[10] & C[10]);
	//C[12] = G3[2] | (P3[2] & C[10]);

	//C[13] = G1[12] | (P1[12] & C[12]);
	//C[14] = G2[6] | (P2[6] & C[12]);
	//C[15] = G1[14] | (P1[14] & C[14]);
	//C[16] = G3[3] | (P3[3] & C[14]);

	//C[17] = G1[16] | (P1[16] & C[16]);
	//C[18] = G2[8] | (P2[8] & C[16]);
	//C[19] = G1[18] | (P1[18] & C[18]);
	//C[20] = G3[4] | (P3[4] & C[18]);

	//C[21] = G1[20] | (P1[20] & C[20]);
	//C[22] = G2[10] | (P2[10] & C[20]);
	//C[23] = G1[22] | (P1[22] & C[22]);
	//C[24] = G3[5] | (P3[5] & C[22]);

	//C[25] = G1[24] | (P1[24] & C[24]);
	//C[26] = G2[12] | (P2[12] & C[24]);
	//C[27] = G1[26] | (P1[26] & C[26]);
	//C[28] = G3[6] | (P3[6] & C[26]);

	//C[29] = G1[28] | (P1[28] & C[28]);
	//C[30] = G2[14] | (P2[14] & C[28]);
	//C[31] = G1[30] | (P1[30] & C[30]);
	//C[32] = G3[7] | (P3[7] & C[30]);

	for (i = 0; i <= 31; i = i + 1)
	{
		S[i] = P1[i] ^ C[i]; //carries and group propagate
	}
	//------------------------------------------
	cout = C[32];

	//WORD c[] = { cout, C[31], C[30], C[29], C[28], C[27], C[26], C[25], C[24],C[23], C[22], C[21], C[20], C[19], C[18], C[17], C[16], C[15], C[14], C[13], C[12], C[11], C[10], C[9], C[8], C[7], C[6], C[5], C[4], C[3], C[2], C[1], C[0] };
	WORD c[] = { cout, S[31], S[30], S[29], S[28], S[27], S[26], S[25], S[24], S[23], S[22], S[21], S[20], S[19], S[18], S[17], S[16], S[15], S[14], S[13], S[12], S[11], S[10], S[9], S[8], S[7], S[6], S[5], S[4], S[3], S[2], S[1], S[0] };
	//WORD c[] = { S[0], S[1], S[2], S[3], S[4], S[5], S[6], S[7], S[8], S[9], S[10], S[11], S[12], S[13], S[14], S[15], S[16], S[17], S[18], S[19], S[20], S[21], S[22], S[23], S[24], S[25], S[26], S[27], S[28], S[29], S[30], S[31], cout };
	//printf("Binary number = %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d \n", cout, S[31], S[30], S[29], S[28], S[27], S[26], S[25], S[24], S[23], S[22], S[21], S[20], S[19], S[18], S[17], S[16], S[15], S[14], S[13], S[12], S[11], S[10], S[9], S[8], S[7], S[6], S[5], S[4], S[3], S[2], S[1], S[0]);

	// convert back to decimal
	int length = sizeof(c) / sizeof(c[0]);
	for (i = 0; i < length; i++)
	{
		if (c[i] == 0)
		{
			u = u * 2;
		}
		else if (c[i] == 1)
		{
			u = u * 2;
			u = u + 1;
		}
		else
		{
			u = u * 2;
		}
	}

	//Calculating value of C-Out
	out = u;
	return out;

}
#pragma endregion

#pragma region BKA32 with k = 16 function
// Approximate BKA32 with K = 16 function
WORD BKA32N16(WORD n, WORD m) // range -4294967296 to 4294967296 each number
{
	//Code for non-approximate Brent-Kung adder, adapted from verilog: https://github.com/Anvesh98/Brentkung-Adder/blob/main/bentkung.v
	//BKA output
	WORD out;
	WORD S[32];

	int i, ii, u = 0;
	WORD a[33] = { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 }, b[33] = { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 };
	WORD cin = 0, cout;
	WORD C[33];

	WORD P1[32], P2[16], P3[8], P4[4];
	WORD G1[32], G2[16], G3[8], G4[4];

	// convert a to binary
	for (i = 0; n > 0; i++)
	{
		a[i] = n % 2;
		n = n / 2;
	}
	// convert b to binary
	for (ii = 0; m > 0; ii++)
	{
		b[ii] = m % 2;
		m = m / 2;
	}

	//^ is bitwise XOR
	// & is bitwise AND
	// | is bitwise OR
	// 

	//Pre-processing stage ---------------------
	//Generate 1st order P's and G's
	C[0] = cin;
	int l = 0;
	for (l = 0; l <= 31; l = l + 1)
	{
		P1[l] = a[l] ^ b[l];
		G1[l] = a[l] & b[l];
	}
	//------------------------------------------

	//Garry Generation Network -----------------
	//Generate 2nd order P's and G's //2nd row
	int len;
	for (len = 0; len <= 15; len = len + 1) // all 2 bit values
	{
		P2[len] = P1[2 * len + 1] & P1[2 * len];
		G2[len] = G1[2 * len + 1] | (P1[2 * len + 1] & G1[2 * len]);
	}

	//Generate 3rd order P's and G's //3rd row
	for (len = 0; len <= 7; len = len + 1) // all 4 bit values
	{
		P3[len] = P2[2 * len + 1] & P2[2 * len];
		G3[len] = G2[2 * len + 1] | (P2[2 * len + 1] & G2[2 * len]);
	}

	//Generate 4th order P's and G's //4th row
	for (len = 0; len <= 3; len = len + 1) // all 8 bit values
	{
		P4[len] = P3[2 * len + 1] & P3[2 * len];
		G4[len] = G3[2 * len + 1] | (P3[2 * len + 1] & G3[2 * len]);
	}

	//Post Processing Stage --------------------
	//Generate all carry signals that can be calculated directly from input
	C[1] = G1[0] | (P1[0] & C[0]);//
	C[2] = G2[0] | (P2[0] & C[0]);//
	C[4] = G3[0] | (P3[0] & C[0]);//

	//Now generating remaining carries
	C[3] = G1[2] | (P1[2] & C[2]); //
	C[5] = G1[4] | (P1[4] & C[4]); //
	C[6] = G2[2] | (P2[2] & C[4]); //
	C[7] = G1[6] | (P1[6] & C[6]); //
	C[8] = G4[0] | (P4[0] & C[4]); //
	C[9] = G1[8] | (P1[8] & C[8]); //
	C[10] = G2[4] | (P2[4] & C[8]); //
	C[11] = G1[10] | (P1[10] & C[10]);// 
	C[12] = G3[2] | (P3[2] & C[8]); //
	C[13] = G1[12] | (P1[12] & C[12]); //
	C[14] = G2[6] | (P2[6] & C[12]);//
	C[15] = G1[14] | (P1[14] & C[14]);//

	C[16] = G4[1] | (P4[1] & C[0]);  //Root Carry 16
	C[17] = G1[16] | (P1[16] & C[16]);
	C[18] = G2[8] | (P2[8] & C[16]); 
	C[19] = G1[18] | (P1[18] & C[18]); 
	C[20] = G3[4] | (P3[4] & C[16]);  
	C[21] = G1[20] | (P1[20] & C[20]); 
	C[22] = G2[10] | (P2[10] & C[20]); 
	C[23] = G1[22] | (P1[22] & C[22]); 

	C[24] = G4[2] | (P4[2] & C[20]); //Root Carry 24 
	C[25] = G1[24] | (P1[24] & C[24]); 
	C[26] = G2[12] | (P2[12] & C[24]); 
	C[27] = G1[26] | (P1[26] & C[26]); 
	C[28] = G3[6] | (P3[6] & C[24]); 
	C[29] = G1[28] | (P1[28] & C[28]); 
	C[30] = G2[14] | (P2[14] & C[28]); 
	C[31] = G1[30] | (P1[30] & C[30]); 

	C[32] = G4[3] | (P4[3] & C[25]); 

	////Post Processing Stage --------------------
	////Generate all carry signals that can be calculated directly from input
	//C[1] = G1[0] | (P1[0] & C[0]);
	//C[2] = G2[0] | (P2[0] & C[0]);
	//C[4] = G3[0] | (P3[0] & C[0]);
	//C[8] = G4[0] | (P4[0] & C[4]);
	//C[12] = G3[2] | (P3[2] & C[8]);
	//C[14] = G2[6] | (P2[6] & C[12]);
	//C[15] = G1[14] | (P1[14] & C[14]);

	////Now generating remaining carries
	//C[3] = G1[2] | (P1[2] & C[2]);
	//C[5] = G1[4] | (P1[4] & C[4]);
	//C[6] = G2[2] | (P2[2] & C[4]);
	//C[7] = G1[6] | (P1[6] & C[6]);
	//C[9] = G1[8] | (P1[8] & C[8]);
	//C[10] = G2[4] | (P2[4] & C[8]);
	//C[11] = G1[10] | (P1[10] & C[10]);
	//C[13] = G1[12] | (P1[12] & C[12]);
	//C[16] = G4[1] | (P4[1] & C[12]);
	//C[17] = G1[16] | (P1[16] & C[16]);
	//C[18] = G2[8] | (P2[8] & C[16]);
	//C[19] = G1[18] | (P1[18] & C[18]);
	//C[20] = G3[4] | (P3[4] & C[16]);
	//C[21] = G1[20] | (P1[20] & C[20]);
	//C[22] = G2[10] | (P2[10] & C[20]);
	//C[23] = G1[22] | (P1[22] & C[22]);
	//C[24] = G4[2] | (P4[2] & C[20]);
	//C[25] = G1[24] | (P1[24] & C[24]);
	//C[26] = G2[12] | (P2[12] & C[24]);
	//C[27] = G1[26] | (P1[26] & C[26]);
	//C[28] = G3[6] | (P3[6] & C[24]);
	//C[29] = G1[28] | (P1[28] & C[28]);
	//C[30] = G2[14] | (P2[14] & C[28]);
	//C[31] = G1[30] | (P1[30] & C[30]);
	//C[32] = G4[3] | (P4[3] & C[28]);

	for (i = 0; i <= 31; i = i + 1)
	{
		S[i] = P1[i] ^ C[i]; //carries and group propagate
	}
	//------------------------------------------
	cout = C[32];

	//WORD c[] = { cout, C[31], C[30], C[29], C[28], C[27], C[26], C[25], C[24],C[23], C[22], C[21], C[20], C[19], C[18], C[17], C[16], C[15], C[14], C[13], C[12], C[11], C[10], C[9], C[8], C[7], C[6], C[5], C[4], C[3], C[2], C[1], C[0] };
	WORD c[] = { cout, S[31], S[30], S[29], S[28], S[27], S[26], S[25], S[24], S[23], S[22], S[21], S[20], S[19], S[18], S[17], S[16], S[15], S[14], S[13], S[12], S[11], S[10], S[9], S[8], S[7], S[6], S[5], S[4], S[3], S[2], S[1], S[0] };
	//WORD c[] = { S[0], S[1], S[2], S[3], S[4], S[5], S[6], S[7], S[8], S[9], S[10], S[11], S[12], S[13], S[14], S[15], S[16], S[17], S[18], S[19], S[20], S[21], S[22], S[23], S[24], S[25], S[26], S[27], S[28], S[29], S[30], S[31], cout };
	//printf("Binary number = %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d \n", cout, S[31], S[30], S[29], S[28], S[27], S[26], S[25], S[24], S[23], S[22], S[21], S[20], S[19], S[18], S[17], S[16], S[15], S[14], S[13], S[12], S[11], S[10], S[9], S[8], S[7], S[6], S[5], S[4], S[3], S[2], S[1], S[0]);

	// convert back to decimal
	int length = sizeof(c) / sizeof(c[0]);
	for (i = 0; i < length; i++)
	{
		if (c[i] == 0)
		{
			u = u * 2;
		}
		else if (c[i] == 1)
		{
			u = u * 2;
			u = u + 1;
		}
		else
		{
			u = u * 2;
		}
	}

	//Calculating value of C-Out
	out = u;
	return out;
}
#pragma endregion

//Cost Functions
//These will need edited with BKA statistics

#pragma region Cost functions
// Original cost for SHA256 with KSA32 adders
float electricity(float a)
{
	// a = error rate

	float cost;
	float power = 5.445; // power consumption per hr
	float elec = 0.1042; // electricity cost in USA (Kwh)
	float day = 24; // 24hr in a day

	float p1 = 17.33; // power(mW) in KSA32
	float p2 = 19; // power(mW) in KSA32(k=16)
	float p3 = 20.4; // power(mW) in KSA32(k=8)
	if (a == 0)
	{
		cost = (power * elec) * day; // power consumption cost per day for SHA256 with normal BKA 32 adder
	}
	else if (a < 0.5)
	{
		cost = ((power * (p2/p1)) * elec) * day; // scaling up for BKA32(k=16) 
	}
	else
	{
		cost = ((power * (p3 / p1)) * elec) * day; // scaling up for BKA32(k=8) 
    }

	return cost;
}
float totalrevenue(float a,float b)
{
	// a = error rate
	// b = electricity cost

	float h = 198; // hash rate
	float h1, h2; // hash rate for KSA32(k=16) & KSA32(k=8)
	float y = 0.203; // Mining yield y(t) (USD/Thash) per day

	float e; // error rate for two rounds (cumulative error rate)

	float area1 = 48801; // area in KSA32
	float area2 = 47829; // reduced area in KSA32(k=16)
	float area3 = 46299; // reduced area in KSA32(k = 8)

	float delay1 = 1.86; // delay in KSA32
	float delay2 = 1.73; // reduced delay in KSA32(k=16)
	float delay3 = 1.58; // reduced delay in KSA32(k = 8)
	float revenue;
	

	e = 1 - ((1-a) * (1-a)); // error rate for two rounds (cumulative error rate)

	if (a == 0)
	{
		revenue = (h*y);
	}
	else if (a < 0.5)
	{
		h1 = ((1 - e)/(area2/area1))*h*((delay1/delay2)); // calculate hash rate with reduced area & delay for KSA32(k=16)
		revenue = (h1*y);
	}
	else
	{
		h2 = ((1 - e)/(area3/area1))*h*(delay1/delay3); // calculate hash rate with reduced area & delay for KSA32(k=8)
		revenue = (h2 * y);
	}
	return revenue;
}
float totalprofit(float a, float b)
{
	// a = revenue
	// b = electricity cost

	float profit; // profit
	profit = a - b;

	return profit;
}
// Cost for SHA256 with Approximate adders
#pragma endregion

//SHA256 Code

#pragma region SHA256 code with KSA32 non-approximate adder
// SHA256 with KSA32 adder
void sha256_transform(SHA256_CTX* ctx, const BYTE data[]) // with CLA adder
{

	// original
	//WORD t1, t2,a;

	WORD b, c, d, e, f, g, h, i, j, m[64];
	// edited
	WORD L1, L11, L2, L22, a1, a0;
	//expander adders
	WORD inp1, inp2, inp3, inp11, inp22, inp33;
	WORD sum1, cout1, sum2, cout2, CPAexpout;

	//compressor adders
	//path 1
	WORD csa1, csa2, csa3, csa11, csa22, csa33, csa111, csa222, csa333, csa1111, csa2222, csa3333;
	WORD csasum1, csacout1, csasum2, csacout2, csasum3, csacout3, csasum4, csacout4;
	//path 2
	WORD csaa1, csaa2, csaa3, csaa11, csaa22, csaa33, csaa111, csaa222, csaa333, csaa1111, csaa2222, csaa3333;
	WORD csaasum1, csaacout1, csaasum2, csaacout2, csaasum3, csaacout3, csaasum4, csaacout4;
	WORD CPAcomp1, CPAcomp2;

	for (i = 0, j = 0; i < 16; ++i, j += 4)
		m[i] = (data[j] << 24) | (data[j + 1] << 16) | (data[j + 2] << 8) | (data[j + 3]);

	for (; i < 64; ++i)
	{

		// CSA 1
		inp1 = m[i - 7];
		inp2 = SIG0(m[i - 15]);
		inp3 = m[i - 16];
		// Calculating value of CSA 1sum
		sum1 = CSAsum(inp1, inp2, inp3);
		//Calculating value of CSA 1 C-Out
		cout1 = CSAcout(inp1, inp2, inp3);

		// CSA 2
		inp11 = SIG1(m[i - 2]);
		inp22 = sum1;
		inp33 = cout1;
		// Calculating value of CSA 2 sum
		sum2 = CSAsum(inp11, inp22, inp33);
		//Calculating value of CSA 2 C-Out
		cout2 = CSAcout(inp11, inp22, inp33);

		// 2) KSA32 exp
		// Calculating value of KSA32 output
		CPAexpout = BKA32(sum2, cout2);

		// Edited SHA256
		m[i] = CPAexpout;
	}

	a0 = ctx->a0[0];
	a1 = ctx->state[0];
	b = ctx->state[1];
	c = ctx->state[2];
	d = ctx->state[3];
	e = ctx->state[4];
	f = ctx->state[5];
	g = ctx->state[6];
	h = ctx->state[7];

	L1 = 0;
	L11 = 0;
	L2 = 0;
	L22 = 0;

	for (i = 0;i < 1; ++i)
	{
		// Path 1
		// CSA 1 & mux
		csa1 = h;

		csa2 = k[i];

		csa3 = m[i];

		// Calculating value of CSA 1sum
		csasum1 = CSAsum(csa1, csa2, csa3);
		//Calculating value of CSA 1 C-Out
		csacout1 = CSAcout(csa1, csa2, csa3);

		// CSA 2 & mux
		csa11 = d;
		csa22 = csasum1;
		csa33 = csacout1;
		// Calculating value of CSA 2 sum
		csasum2 = CSAsum(csa11, csa22, csa33);
		//Calculating value of CSA 2 C-Out
		csacout2 = CSAcout(csa11, csa22, csa33);

		// CSA 3 & L0
		csa111 = CH(e, f, g);
		csa222 = L1;
		csa333 = L11;
		// Calculating value of CSA 2 sum
		csasum3 = CSAsum(csa111, csa222, csa333);
		//Calculating value of CSA 2 C-Out
		csacout3 = CSAcout(csa111, csa222, csa333);

		// CSA 4
		csa1111 = EP1(e);
		csa2222 = csasum3;
		csa3333 = csacout3;
		// Calculating value of CSA 2 sum
		csasum4 = CSAsum(csa1111, csa2222, csa3333);
		//Calculating value of CSA 2 C-Out
		csacout4 = CSAcout(csa1111, csa2222, csa3333);

		// KSA32 comp 1
		// Calculating value of KSA32 output
		CPAcomp1 = BKA32(csasum4, csacout4);




		//path 2
		// need to declare CPAcomp2 first
		/// CPA comp 2
		// Calculating value of KSA32 output
		CPAcomp2 = BKA32(a1, a0);

		// CSA 1 & L1
		csaa1 = CH(e, f, g);
		csaa2 = L2;
		csaa3 = L22;
		// Calculating value of CSA 1sum
		csaasum1 = CSAsum(csaa1, csaa2, csaa3);
		//Calculating value of CSA 1 C-Out
		csaacout1 = CSAcout(csaa1, csaa2, csaa3);

		// CSA 2
		csaa11 = EP1(e);
		csaa22 = csaasum1;
		csaa33 = csaacout1;
		// Calculating value of CSA 2 sum
		csaasum2 = CSAsum(csaa11, csaa22, csaa33);
		//Calculating value of CSA 2 C-Out
		csaacout2 = CSAcout(csaa11, csaa22, csaa33);

		// CSA 3 
		csaa111 = MAJ(CPAcomp2, b, c);
		csaa222 = csaasum2;
		csaa333 = csaacout2;
		// Calculating value of CSA 2 sum
		csaasum3 = CSAsum(csaa111, csaa222, csaa333);
		//Calculating value of CSA 2 C-Out
		csaacout3 = CSAcout(csaa111, csaa222, csaa333);

		// CSA 4
		csaa1111 = EP0(CPAcomp2);
		csaa2222 = csaasum3;
		csaa3333 = csaacout3;
		// Calculating value of CSA 2 sum
		csaasum4 = CSAsum(csaa1111, csaa2222, csaa3333);
		//Calculating value of CSA 2 C-Out
		csaacout4 = CSAcout(csaa1111, csaa2222, csaa3333);

		h = h;
		g = g;
		f = f;
		e = e;

		d = d;
		c = c;
		b = b;
		a1 = a1;
		a0 = a0;

		L1 = csasum2;
		L11 = csacout2;

		L2 = csasum1;
		L22 = csacout1;
	}

	for (; i < 2; ++i)
	{
		// Path 1
	// CSA 1 & mux
		csa1 = g;

		csa2 = k[i];

		csa3 = m[i];

		// Calculating value of CSA 1sum
		csasum1 = CSAsum(csa1, csa2, csa3);
		//Calculating value of CSA 1 C-Out
		csacout1 = CSAcout(csa1, csa2, csa3);

		// CSA 2 & mux
		csa11 = c;
		csa22 = csasum1;
		csa33 = csacout1;
		// Calculating value of CSA 2 sum
		csasum2 = CSAsum(csa11, csa22, csa33);
		//Calculating value of CSA 2 C-Out
		csacout2 = CSAcout(csa11, csa22, csa33);

		// CSA 3 & L0
		csa111 = CH(e, f, g);
		csa222 = L1;
		csa333 = L11;
		// Calculating value of CSA 2 sum
		csasum3 = CSAsum(csa111, csa222, csa333);
		//Calculating value of CSA 2 C-Out
		csacout3 = CSAcout(csa111, csa222, csa333);

		// CSA 4
		csa1111 = EP1(e);
		csa2222 = csasum3;
		csa3333 = csacout3;
		// Calculating value of CSA 2 sum
		csasum4 = CSAsum(csa1111, csa2222, csa3333);
		//Calculating value of CSA 2 C-Out
		csacout4 = CSAcout(csa1111, csa2222, csa3333);

		// CPA comp 1
		// Calculating value of KSA32 output
		CPAcomp1 = BKA32(csasum4, csacout4);




		//path 2
		// need to declare CPAcomp2 first
		/// KSA32 comp 2
		// Calculating value of KSA32 output
		CPAcomp2 = BKA32(a1, a0);

		// CSA 1 & L1
		csaa1 = CH(e, f, g);
		csaa2 = L2;
		csaa3 = L22;
		// Calculating value of CSA 1sum
		csaasum1 = CSAsum(csaa1, csaa2, csaa3);
		//Calculating value of CSA 1 C-Out
		csaacout1 = CSAcout(csaa1, csaa2, csaa3);

		// CSA 2
		csaa11 = EP1(e);
		csaa22 = csaasum1;
		csaa33 = csaacout1;
		// Calculating value of CSA 2 sum
		csaasum2 = CSAsum(csaa11, csaa22, csaa33);
		//Calculating value of CSA 2 C-Out
		csaacout2 = CSAcout(csaa11, csaa22, csaa33);

		// CSA 3 
		csaa111 = MAJ(CPAcomp2, b, c);
		csaa222 = csaasum2;
		csaa333 = csaacout2;
		// Calculating value of CSA 2 sum
		csaasum3 = CSAsum(csaa111, csaa222, csaa333);
		//Calculating value of CSA 2 C-Out
		csaacout3 = CSAcout(csaa111, csaa222, csaa333);

		// CSA 4
		csaa1111 = EP0(CPAcomp2);
		csaa2222 = csaasum3;
		csaa3333 = csaacout3;
		// Calculating value of CSA 2 sum
		csaasum4 = CSAsum(csaa1111, csaa2222, csaa3333);
		//Calculating value of CSA 2 C-Out
		csaacout4 = CSAcout(csaa1111, csaa2222, csaa3333);

		h = g;
		g = f;
		f = e;
		e = CPAcomp1;

		d = c;
		c = b;
		b = CPAcomp2;
		a1 = csaasum4;
		a0 = csaacout4;

		L1 = csasum2;
		L11 = csacout2;

		L2 = csasum1;
		L22 = csacout1;
	}

	for (; i < 64; ++i)
	{
		// Path 1
		// CSA 1 & mux
		csa1 = g;

		csa2 = k[i];

		csa3 = m[i];

		// Calculating value of CSA 1sum
		csasum1 = CSAsum(csa1, csa2, csa3);
		//Calculating value of CSA 1 C-Out
		csacout1 = CSAcout(csa1, csa2, csa3);

		// CSA 2 & mux
		csa11 = c;
		csa22 = csasum1;
		csa33 = csacout1;
		// Calculating value of CSA 2 sum
		csasum2 = CSAsum(csa11, csa22, csa33);
		//Calculating value of CSA 2 C-Out
		csacout2 = CSAcout(csa11, csa22, csa33);

		// CSA 3 & L0
		csa111 = CH(e, f, g);
		csa222 = L1;
		csa333 = L11;
		// Calculating value of CSA 2 sum
		csasum3 = CSAsum(csa111, csa222, csa333);
		//Calculating value of CSA 2 C-Out
		csacout3 = CSAcout(csa111, csa222, csa333);

		// CSA 4
		csa1111 = EP1(e);
		csa2222 = csasum3;
		csa3333 = csacout3;
		// Calculating value of CSA 2 sum
		csasum4 = CSAsum(csa1111, csa2222, csa3333);
		//Calculating value of CSA 2 C-Out
		csacout4 = CSAcout(csa1111, csa2222, csa3333);

		// CPA comp 1
		// Calculating value of KSA32 output
		CPAcomp1 = BKA32(csasum4, csacout4);




		//path 2
		// need to declare CPAcomp2 first
		/// KSA32 comp 2
		// Calculating value of KSA32 output
		CPAcomp2 = BKA32(a1, a0);

		// CSA 1 & L1
		csaa1 = CH(e, f, g);
		csaa2 = L2;
		csaa3 = L22;
		// Calculating value of CSA 1sum
		csaasum1 = CSAsum(csaa1, csaa2, csaa3);
		//Calculating value of CSA 1 C-Out
		csaacout1 = CSAcout(csaa1, csaa2, csaa3);

		// CSA 2
		csaa11 = EP1(e);
		csaa22 = csaasum1;
		csaa33 = csaacout1;
		// Calculating value of CSA 2 sum
		csaasum2 = CSAsum(csaa11, csaa22, csaa33);
		//Calculating value of CSA 2 C-Out
		csaacout2 = CSAcout(csaa11, csaa22, csaa33);

		// CSA 3 
		csaa111 = MAJ(CPAcomp2, b, c);
		csaa222 = csaasum2;
		csaa333 = csaacout2;
		// Calculating value of CSA 2 sum
		csaasum3 = CSAsum(csaa111, csaa222, csaa333);
		//Calculating value of CSA 2 C-Out
		csaacout3 = CSAcout(csaa111, csaa222, csaa333);

		// CSA 4
		csaa1111 = EP0(CPAcomp2);
		csaa2222 = csaasum3;
		csaa3333 = csaacout3;
		// Calculating value of CSA 2 sum
		csaasum4 = CSAsum(csaa1111, csaa2222, csaa3333);
		//Calculating value of CSA 2 C-Out
		csaacout4 = CSAcout(csaa1111, csaa2222, csaa3333);

		h = g;
		g = f;
		f = e;
		e = CPAcomp1;

		d = c;
		c = b;
		b = CPAcomp2;
		a1 = csaasum4;
		a0 = csaacout4;

		L1 = csasum2;
		L11 = csacout2;

		L2 = csasum1;
		L22 = csacout1;
	}

	for (; i < 65; ++i)
	{
		// Path 1
		// CSA 1 & mux
		csa1 = g;

		csa2 = k[i];

		csa3 = m[i];

		//workable
		//csa3 = m[i];

		// Calculating value of CSA 1sum
		csasum1 = CSAsum(csa1, csa2, csa3);
		//Calculating value of CSA 1 C-Out
		csacout1 = CSAcout(csa1, csa2, csa3);

		// CSA 2 & mux
		csa11 = c;
		csa22 = csasum1;
		csa33 = csacout1;
		// Calculating value of CSA 2 sum
		csasum2 = CSAsum(csa11, csa22, csa33);
		//Calculating value of CSA 2 C-Out
		csacout2 = CSAcout(csa11, csa22, csa33);

		// CSA 3 & L0
		csa111 = CH(e, f, g);
		csa222 = L1;
		csa333 = L11;
		// Calculating value of CSA 2 sum
		csasum3 = CSAsum(csa111, csa222, csa333);
		//Calculating value of CSA 2 C-Out
		csacout3 = CSAcout(csa111, csa222, csa333);

		// CSA 4
		csa1111 = EP1(e);
		csa2222 = csasum3;
		csa3333 = csacout3;
		// Calculating value of CSA 2 sum
		csasum4 = CSAsum(csa1111, csa2222, csa3333);
		//Calculating value of CSA 2 C-Out
		csacout4 = CSAcout(csa1111, csa2222, csa3333);

		// CPA comp 1
		// Calculating value of KSA32 output
		CPAcomp1 = BKA32(csasum4, csacout4);


		//path 2
		// need to declare CPAcomp2 first
		/// KSA32 comp 2
		// Calculating value of KSA32 output
		CPAcomp2 = BKA32(a1, a0);

		// CSA 1 & L1
		csaa1 = CH(e, f, g);
		csaa2 = L2;
		csaa3 = L22;
		// Calculating value of CSA 1sum
		csaasum1 = CSAsum(csaa1, csaa2, csaa3);
		//Calculating value of CSA 1 C-Out
		csaacout1 = CSAcout(csaa1, csaa2, csaa3);

		// CSA 2
		csaa11 = EP1(e);
		csaa22 = csaasum1;
		csaa33 = csaacout1;
		// Calculating value of CSA 2 sum
		csaasum2 = CSAsum(csaa11, csaa22, csaa33);
		//Calculating value of CSA 2 C-Out
		csaacout2 = CSAcout(csaa11, csaa22, csaa33);

		// CSA 3 
		csaa111 = MAJ(CPAcomp2, b, c);
		csaa222 = csaasum2;
		csaa333 = csaacout2;
		// Calculating value of CSA 2 sum
		csaasum3 = CSAsum(csaa111, csaa222, csaa333);
		//Calculating value of CSA 2 C-Out
		csaacout3 = CSAcout(csaa111, csaa222, csaa333);

		// CSA 4
		csaa1111 = EP0(CPAcomp2);
		csaa2222 = csaasum3;
		csaa3333 = csaacout3;
		// Calculating value of CSA 2 sum
		csaasum4 = CSAsum(csaa1111, csaa2222, csaa3333);
		//Calculating value of CSA 2 C-Out
		csaacout4 = CSAcout(csaa1111, csaa2222, csaa3333);

		h = g;
		g = f;
		f = e;
		e = CPAcomp1;

		d = c;
		c = b;
		b = CPAcomp2;
		a1 = csaasum4;
		a0 = csaacout4;
		a1 = BKA32(a1, a0);
		a0 = 0;


		L1 = csasum2;
		L11 = csacout2;

		L2 = csasum1;
		L22 = csacout1;
	}

	ctx->a0[0] += a0;
	ctx->state[0] += a1;
	ctx->state[1] += b;
	ctx->state[2] += c;
	ctx->state[3] += d;
	ctx->state[4] += e;
	ctx->state[5] += f;
	ctx->state[6] += g;
	ctx->state[7] += h;
}
void sha256_init(SHA256_CTX* ctx)
{
	ctx->datalen = 0;
	ctx->bitlen = 0;

	ctx->a0[0] = 0x00000000;
	ctx->state[0] = 0x6a09e667;
	ctx->state[1] = 0xbb67ae85;
	ctx->state[2] = 0x3c6ef372;
	ctx->state[3] = 0xa54ff53a;
	ctx->state[4] = 0x510e527f;
	ctx->state[5] = 0x9b05688c;
	ctx->state[6] = 0x1f83d9ab;
	ctx->state[7] = 0x5be0cd19;
}
void sha256_update(SHA256_CTX* ctx, const BYTE data[], size_t len)
{
	WORD i;

	for (i = 0; i < len; ++i) {
		ctx->data[ctx->datalen] = data[i];
		ctx->datalen++;
		if (ctx->datalen == 64) {
			sha256_transform(ctx, ctx->data);
			ctx->bitlen += 512;
			ctx->datalen = 0;
		}
	}
}
void sha256_final(SHA256_CTX* ctx, BYTE hash[])
{
	WORD i;

	i = ctx->datalen;

	// Pad whatever data is left in the buffer.
	if (ctx->datalen < 56) {
		ctx->data[i++] = 0x80;
		while (i < 56)
			ctx->data[i++] = 0x00;
	}
	else {
		ctx->data[i++] = 0x80;
		while (i < 64)
			ctx->data[i++] = 0x00;
		sha256_transform(ctx, ctx->data);
		memset(ctx->data, 0, 56);
	}

	// Append to the padding the total message's length in bits and transform.
	ctx->bitlen += ctx->datalen * 8;
	ctx->data[63] = ctx->bitlen;
	ctx->data[62] = ctx->bitlen >> 8;
	ctx->data[61] = ctx->bitlen >> 16;
	ctx->data[60] = ctx->bitlen >> 24;
	ctx->data[59] = ctx->bitlen >> 32;
	ctx->data[58] = ctx->bitlen >> 40;
	ctx->data[57] = ctx->bitlen >> 48;
	ctx->data[56] = ctx->bitlen >> 56;
	sha256_transform(ctx, ctx->data);

	// Since this implementation uses little endian byte ordering and SHA uses big endian,
	// reverse all the bytes when copying the final state to the output hash.
	for (i = 0; i < 4; ++i) {

		hash[i] = (ctx->state[0] >> (24 - i * 8)) & 0x000000ff;
		hash[i + 4] = (ctx->state[1] >> (24 - i * 8)) & 0x000000ff;
		hash[i + 8] = (ctx->state[2] >> (24 - i * 8)) & 0x000000ff;
		hash[i + 12] = (ctx->state[3] >> (24 - i * 8)) & 0x000000ff;
		hash[i + 16] = (ctx->state[4] >> (24 - i * 8)) & 0x000000ff;
		hash[i + 20] = (ctx->state[5] >> (24 - i * 8)) & 0x000000ff;
		hash[i + 24] = (ctx->state[6] >> (24 - i * 8)) & 0x000000ff;
		hash[i + 28] = (ctx->state[7] >> (24 - i * 8)) & 0x000000ff;

	}
}
#pragma endregion

#pragma region SHA256 code with approximate BKA32(K=8) adder
// SHA256 with approximate BKA32(K=8) adder
void sha256_transformBKA32N8(SHA256_CTX1* ctx1, const BYTE data[]) // with CLA adder
{

	// original
	//WORD t1, t2,a;

	WORD b, c, d, e, f, g, h, i, j, m[64];
	// edited
	WORD L1, L11, L2, L22, a1, a0;
	//expander adders
	WORD inp1, inp2, inp3, inp11, inp22, inp33;
	WORD sum1, cout1, sum2, cout2, CPAexpout;

	//compressor adders
	//path 1
	WORD csa1, csa2, csa3, csa11, csa22, csa33, csa111, csa222, csa333, csa1111, csa2222, csa3333;
	WORD csasum1, csacout1, csasum2, csacout2, csasum3, csacout3, csasum4, csacout4;
	//path 2
	WORD csaa1, csaa2, csaa3, csaa11, csaa22, csaa33, csaa111, csaa222, csaa333, csaa1111, csaa2222, csaa3333;
	WORD csaasum1, csaacout1, csaasum2, csaacout2, csaasum3, csaacout3, csaasum4, csaacout4;
	WORD CPAcomp1, CPAcomp2;

	for (i = 0, j = 0; i < 16; ++i, j += 4)
		m[i] = (data[j] << 24) | (data[j + 1] << 16) | (data[j + 2] << 8) | (data[j + 3]);

	for (; i < 64; ++i)
	{

		// CSA 1
		inp1 = m[i - 7];
		inp2 = SIG0(m[i - 15]);
		inp3 = m[i - 16];
		// Calculating value of CSA 1sum
		sum1 = CSAsum(inp1, inp2, inp3);
		//Calculating value of CSA 1 C-Out
		cout1 = CSAcout(inp1, inp2, inp3);

		// CSA 2
		inp11 = SIG1(m[i - 2]);
		inp22 = sum1;
		inp33 = cout1;
		// Calculating value of CSA 2 sum
		sum2 = CSAsum(inp11, inp22, inp33);
		//Calculating value of CSA 2 C-Out
		cout2 = CSAcout(inp11, inp22, inp33);

		// 2) BKA32 exp
		// Calculating value of BKA32 output
		CPAexpout = BKA32N8(sum2, cout2);

		// Edited SHA256
		m[i] = CPAexpout;
	}

	a0 = ctx1->a0[0];
	a1 = ctx1->state[0];
	b = ctx1->state[1];
	c = ctx1->state[2];
	d = ctx1->state[3];
	e = ctx1->state[4];
	f = ctx1->state[5];
	g = ctx1->state[6];
	h = ctx1->state[7];

	L1 = 0;
	L11 = 0;
	L2 = 0;
	L22 = 0;

	for (i = 0;i < 1; ++i)
	{
		// Path 1
		// CSA 1 & mux
		csa1 = h;

		csa2 = k[i];

		csa3 = m[i];

		// Calculating value of CSA 1sum
		csasum1 = CSAsum(csa1, csa2, csa3);
		//Calculating value of CSA 1 C-Out
		csacout1 = CSAcout(csa1, csa2, csa3);

		// CSA 2 & mux
		csa11 = d;
		csa22 = csasum1;
		csa33 = csacout1;
		// Calculating value of CSA 2 sum
		csasum2 = CSAsum(csa11, csa22, csa33);
		//Calculating value of CSA 2 C-Out
		csacout2 = CSAcout(csa11, csa22, csa33);

		// CSA 3 & L0
		csa111 = CH(e, f, g);
		csa222 = L1;
		csa333 = L11;
		// Calculating value of CSA 2 sum
		csasum3 = CSAsum(csa111, csa222, csa333);
		//Calculating value of CSA 2 C-Out
		csacout3 = CSAcout(csa111, csa222, csa333);

		// CSA 4
		csa1111 = EP1(e);
		csa2222 = csasum3;
		csa3333 = csacout3;
		// Calculating value of CSA 2 sum
		csasum4 = CSAsum(csa1111, csa2222, csa3333);
		//Calculating value of CSA 2 C-Out
		csacout4 = CSAcout(csa1111, csa2222, csa3333);

		// KSA32 comp 1
		// Calculating value of KSA32 output
		CPAcomp1 = BKA32N8(csasum4, csacout4);




		//path 2
		// need to declare CPAcomp2 first
		/// CPA comp 2
		// Calculating value of KSA32 output
		CPAcomp2 = BKA32N8(a1, a0);

		// CSA 1 & L1
		csaa1 = CH(e, f, g);
		csaa2 = L2;
		csaa3 = L22;
		// Calculating value of CSA 1sum
		csaasum1 = CSAsum(csaa1, csaa2, csaa3);
		//Calculating value of CSA 1 C-Out
		csaacout1 = CSAcout(csaa1, csaa2, csaa3);

		// CSA 2
		csaa11 = EP1(e);
		csaa22 = csaasum1;
		csaa33 = csaacout1;
		// Calculating value of CSA 2 sum
		csaasum2 = CSAsum(csaa11, csaa22, csaa33);
		//Calculating value of CSA 2 C-Out
		csaacout2 = CSAcout(csaa11, csaa22, csaa33);

		// CSA 3 
		csaa111 = MAJ(CPAcomp2, b, c);
		csaa222 = csaasum2;
		csaa333 = csaacout2;
		// Calculating value of CSA 2 sum
		csaasum3 = CSAsum(csaa111, csaa222, csaa333);
		//Calculating value of CSA 2 C-Out
		csaacout3 = CSAcout(csaa111, csaa222, csaa333);

		// CSA 4
		csaa1111 = EP0(CPAcomp2);
		csaa2222 = csaasum3;
		csaa3333 = csaacout3;
		// Calculating value of CSA 2 sum
		csaasum4 = CSAsum(csaa1111, csaa2222, csaa3333);
		//Calculating value of CSA 2 C-Out
		csaacout4 = CSAcout(csaa1111, csaa2222, csaa3333);

		h = h;
		g = g;
		f = f;
		e = e;

		d = d;
		c = c;
		b = b;
		a1 = a1;
		a0 = a0;

		L1 = csasum2;
		L11 = csacout2;

		L2 = csasum1;
		L22 = csacout1;
	}

	for (; i < 2; ++i)
	{
		// Path 1
	// CSA 1 & mux
		csa1 = g;

		csa2 = k[i];

		csa3 = m[i];

		// Calculating value of CSA 1sum
		csasum1 = CSAsum(csa1, csa2, csa3);
		//Calculating value of CSA 1 C-Out
		csacout1 = CSAcout(csa1, csa2, csa3);

		// CSA 2 & mux
		csa11 = c;
		csa22 = csasum1;
		csa33 = csacout1;
		// Calculating value of CSA 2 sum
		csasum2 = CSAsum(csa11, csa22, csa33);
		//Calculating value of CSA 2 C-Out
		csacout2 = CSAcout(csa11, csa22, csa33);

		// CSA 3 & L0
		csa111 = CH(e, f, g);
		csa222 = L1;
		csa333 = L11;
		// Calculating value of CSA 2 sum
		csasum3 = CSAsum(csa111, csa222, csa333);
		//Calculating value of CSA 2 C-Out
		csacout3 = CSAcout(csa111, csa222, csa333);

		// CSA 4
		csa1111 = EP1(e);
		csa2222 = csasum3;
		csa3333 = csacout3;
		// Calculating value of CSA 2 sum
		csasum4 = CSAsum(csa1111, csa2222, csa3333);
		//Calculating value of CSA 2 C-Out
		csacout4 = CSAcout(csa1111, csa2222, csa3333);

		// CPA comp 1
		// Calculating value of KSA32 output
		CPAcomp1 = BKA32N8(csasum4, csacout4);




		//path 2
		// need to declare CPAcomp2 first
		/// KSA32 comp 2
		// Calculating value of KSA32 output
		CPAcomp2 = BKA32N8(a1, a0);

		// CSA 1 & L1
		csaa1 = CH(e, f, g);
		csaa2 = L2;
		csaa3 = L22;
		// Calculating value of CSA 1sum
		csaasum1 = CSAsum(csaa1, csaa2, csaa3);
		//Calculating value of CSA 1 C-Out
		csaacout1 = CSAcout(csaa1, csaa2, csaa3);

		// CSA 2
		csaa11 = EP1(e);
		csaa22 = csaasum1;
		csaa33 = csaacout1;
		// Calculating value of CSA 2 sum
		csaasum2 = CSAsum(csaa11, csaa22, csaa33);
		//Calculating value of CSA 2 C-Out
		csaacout2 = CSAcout(csaa11, csaa22, csaa33);

		// CSA 3 
		csaa111 = MAJ(CPAcomp2, b, c);
		csaa222 = csaasum2;
		csaa333 = csaacout2;
		// Calculating value of CSA 2 sum
		csaasum3 = CSAsum(csaa111, csaa222, csaa333);
		//Calculating value of CSA 2 C-Out
		csaacout3 = CSAcout(csaa111, csaa222, csaa333);

		// CSA 4
		csaa1111 = EP0(CPAcomp2);
		csaa2222 = csaasum3;
		csaa3333 = csaacout3;
		// Calculating value of CSA 2 sum
		csaasum4 = CSAsum(csaa1111, csaa2222, csaa3333);
		//Calculating value of CSA 2 C-Out
		csaacout4 = CSAcout(csaa1111, csaa2222, csaa3333);

		h = g;
		g = f;
		f = e;
		e = CPAcomp1;

		d = c;
		c = b;
		b = CPAcomp2;
		a1 = csaasum4;
		a0 = csaacout4;

		L1 = csasum2;
		L11 = csacout2;

		L2 = csasum1;
		L22 = csacout1;
	}

	for (; i < 64; ++i)
	{
		// Path 1
		// CSA 1 & mux
		csa1 = g;

		csa2 = k[i];

		csa3 = m[i];

		// Calculating value of CSA 1sum
		csasum1 = CSAsum(csa1, csa2, csa3);
		//Calculating value of CSA 1 C-Out
		csacout1 = CSAcout(csa1, csa2, csa3);

		// CSA 2 & mux
		csa11 = c;
		csa22 = csasum1;
		csa33 = csacout1;
		// Calculating value of CSA 2 sum
		csasum2 = CSAsum(csa11, csa22, csa33);
		//Calculating value of CSA 2 C-Out
		csacout2 = CSAcout(csa11, csa22, csa33);

		// CSA 3 & L0
		csa111 = CH(e, f, g);
		csa222 = L1;
		csa333 = L11;
		// Calculating value of CSA 2 sum
		csasum3 = CSAsum(csa111, csa222, csa333);
		//Calculating value of CSA 2 C-Out
		csacout3 = CSAcout(csa111, csa222, csa333);

		// CSA 4
		csa1111 = EP1(e);
		csa2222 = csasum3;
		csa3333 = csacout3;
		// Calculating value of CSA 2 sum
		csasum4 = CSAsum(csa1111, csa2222, csa3333);
		//Calculating value of CSA 2 C-Out
		csacout4 = CSAcout(csa1111, csa2222, csa3333);

		// CPA comp 1
		// Calculating value of KSA32 output
		CPAcomp1 = BKA32N8(csasum4, csacout4);




		//path 2
		// need to declare CPAcomp2 first
		/// KSA32 comp 2
		// Calculating value of KSA32 output
		CPAcomp2 = BKA32N8(a1, a0);

		// CSA 1 & L1
		csaa1 = CH(e, f, g);
		csaa2 = L2;
		csaa3 = L22;
		// Calculating value of CSA 1sum
		csaasum1 = CSAsum(csaa1, csaa2, csaa3);
		//Calculating value of CSA 1 C-Out
		csaacout1 = CSAcout(csaa1, csaa2, csaa3);

		// CSA 2
		csaa11 = EP1(e);
		csaa22 = csaasum1;
		csaa33 = csaacout1;
		// Calculating value of CSA 2 sum
		csaasum2 = CSAsum(csaa11, csaa22, csaa33);
		//Calculating value of CSA 2 C-Out
		csaacout2 = CSAcout(csaa11, csaa22, csaa33);

		// CSA 3 
		csaa111 = MAJ(CPAcomp2, b, c);
		csaa222 = csaasum2;
		csaa333 = csaacout2;
		// Calculating value of CSA 2 sum
		csaasum3 = CSAsum(csaa111, csaa222, csaa333);
		//Calculating value of CSA 2 C-Out
		csaacout3 = CSAcout(csaa111, csaa222, csaa333);

		// CSA 4
		csaa1111 = EP0(CPAcomp2);
		csaa2222 = csaasum3;
		csaa3333 = csaacout3;
		// Calculating value of CSA 2 sum
		csaasum4 = CSAsum(csaa1111, csaa2222, csaa3333);
		//Calculating value of CSA 2 C-Out
		csaacout4 = CSAcout(csaa1111, csaa2222, csaa3333);

		h = g;
		g = f;
		f = e;
		e = CPAcomp1;

		d = c;
		c = b;
		b = CPAcomp2;
		a1 = csaasum4;
		a0 = csaacout4;

		L1 = csasum2;
		L11 = csacout2;

		L2 = csasum1;
		L22 = csacout1;
	}

	for (; i < 65; ++i)
	{
		// Path 1
		// CSA 1 & mux
		csa1 = g;

		csa2 = k[i];

		csa3 = m[i];

		//workable
		//csa3 = m[i];

		// Calculating value of CSA 1sum
		csasum1 = CSAsum(csa1, csa2, csa3);
		//Calculating value of CSA 1 C-Out
		csacout1 = CSAcout(csa1, csa2, csa3);

		// CSA 2 & mux
		csa11 = c;
		csa22 = csasum1;
		csa33 = csacout1;
		// Calculating value of CSA 2 sum
		csasum2 = CSAsum(csa11, csa22, csa33);
		//Calculating value of CSA 2 C-Out
		csacout2 = CSAcout(csa11, csa22, csa33);

		// CSA 3 & L0
		csa111 = CH(e, f, g);
		csa222 = L1;
		csa333 = L11;
		// Calculating value of CSA 2 sum
		csasum3 = CSAsum(csa111, csa222, csa333);
		//Calculating value of CSA 2 C-Out
		csacout3 = CSAcout(csa111, csa222, csa333);

		// CSA 4
		csa1111 = EP1(e);
		csa2222 = csasum3;
		csa3333 = csacout3;
		// Calculating value of CSA 2 sum
		csasum4 = CSAsum(csa1111, csa2222, csa3333);
		//Calculating value of CSA 2 C-Out
		csacout4 = CSAcout(csa1111, csa2222, csa3333);

		// CPA comp 1
		// Calculating value of KSA32 output
		CPAcomp1 = BKA32N8(csasum4, csacout4);


		//path 2
		// need to declare CPAcomp2 first
		/// KSA32 comp 2
		// Calculating value of KSA32 output
		CPAcomp2 = BKA32N8(a1, a0);

		// CSA 1 & L1
		csaa1 = CH(e, f, g);
		csaa2 = L2;
		csaa3 = L22;
		// Calculating value of CSA 1sum
		csaasum1 = CSAsum(csaa1, csaa2, csaa3);
		//Calculating value of CSA 1 C-Out
		csaacout1 = CSAcout(csaa1, csaa2, csaa3);

		// CSA 2
		csaa11 = EP1(e);
		csaa22 = csaasum1;
		csaa33 = csaacout1;
		// Calculating value of CSA 2 sum
		csaasum2 = CSAsum(csaa11, csaa22, csaa33);
		//Calculating value of CSA 2 C-Out
		csaacout2 = CSAcout(csaa11, csaa22, csaa33);

		// CSA 3 
		csaa111 = MAJ(CPAcomp2, b, c);
		csaa222 = csaasum2;
		csaa333 = csaacout2;
		// Calculating value of CSA 2 sum
		csaasum3 = CSAsum(csaa111, csaa222, csaa333);
		//Calculating value of CSA 2 C-Out
		csaacout3 = CSAcout(csaa111, csaa222, csaa333);

		// CSA 4
		csaa1111 = EP0(CPAcomp2);
		csaa2222 = csaasum3;
		csaa3333 = csaacout3;
		// Calculating value of CSA 2 sum
		csaasum4 = CSAsum(csaa1111, csaa2222, csaa3333);
		//Calculating value of CSA 2 C-Out
		csaacout4 = CSAcout(csaa1111, csaa2222, csaa3333);

		h = g;
		g = f;
		f = e;
		e = CPAcomp1;

		d = c;
		c = b;
		b = CPAcomp2;
		a1 = csaasum4;
		a0 = csaacout4;
		a1 = BKA32N8(a1, a0);
		a0 = 0;


		L1 = csasum2;
		L11 = csacout2;

		L2 = csasum1;
		L22 = csacout1;
	}

	ctx1->a0[0] += a0;
	ctx1->state[0] += a1;
	ctx1->state[1] += b;
	ctx1->state[2] += c;
	ctx1->state[3] += d;
	ctx1->state[4] += e;
	ctx1->state[5] += f;
	ctx1->state[6] += g;
	ctx1->state[7] += h;
}
void sha256_initBKA32N8(SHA256_CTX1* ctx1)
{
	ctx1->datalen = 0;
	ctx1->bitlen = 0;

	ctx1->a0[0] = 0x00000000;
	ctx1->state[0] = 0x6a09e667;
	ctx1->state[1] = 0xbb67ae85;
	ctx1->state[2] = 0x3c6ef372;
	ctx1->state[3] = 0xa54ff53a;
	ctx1->state[4] = 0x510e527f;
	ctx1->state[5] = 0x9b05688c;
	ctx1->state[6] = 0x1f83d9ab;
	ctx1->state[7] = 0x5be0cd19;
}
void sha256_updateBKA32N8(SHA256_CTX1* ctx1, const BYTE data[], size_t len)
{
	WORD i;

	for (i = 0; i < len; ++i) {
		ctx1->data[ctx1->datalen] = data[i];
		ctx1->datalen++;
		if (ctx1->datalen == 64) {
			sha256_transformBKA32N8(ctx1, ctx1->data);
			ctx1->bitlen += 512;
			ctx1->datalen = 0;
		}
	}
}
void sha256_finalBKA32N8(SHA256_CTX1* ctx1, BYTE hash[])
{
	WORD i;

	i = ctx1->datalen;

	// Pad whatever data is left in the buffer.
	if (ctx1->datalen < 56) {
		ctx1->data[i++] = 0x80;
		while (i < 56)
			ctx1->data[i++] = 0x00;
	}
	else {
		ctx1->data[i++] = 0x80;
		while (i < 64)
			ctx1->data[i++] = 0x00;
		sha256_transformBKA32N8(ctx1, ctx1->data);
		memset(ctx1->data, 0, 56);
	}

	// Append to the padding the total message's length in bits and transform.
	ctx1->bitlen += ctx1->datalen * 8;
	ctx1->data[63] = ctx1->bitlen;
	ctx1->data[62] = ctx1->bitlen >> 8;
	ctx1->data[61] = ctx1->bitlen >> 16;
	ctx1->data[60] = ctx1->bitlen >> 24;
	ctx1->data[59] = ctx1->bitlen >> 32;
	ctx1->data[58] = ctx1->bitlen >> 40;
	ctx1->data[57] = ctx1->bitlen >> 48;
	ctx1->data[56] = ctx1->bitlen >> 56;
	sha256_transformBKA32N8(ctx1, ctx1->data);

	// Since this implementation uses little endian byte ordering and SHA uses big endian,
	// reverse all the bytes when copying the final state to the output hash.
	for (i = 0; i < 4; ++i) {

		hash[i] = (ctx1->state[0] >> (24 - i * 8)) & 0x000000ff;
		hash[i + 4] = (ctx1->state[1] >> (24 - i * 8)) & 0x000000ff;
		hash[i + 8] = (ctx1->state[2] >> (24 - i * 8)) & 0x000000ff;
		hash[i + 12] = (ctx1->state[3] >> (24 - i * 8)) & 0x000000ff;
		hash[i + 16] = (ctx1->state[4] >> (24 - i * 8)) & 0x000000ff;
		hash[i + 20] = (ctx1->state[5] >> (24 - i * 8)) & 0x000000ff;
		hash[i + 24] = (ctx1->state[6] >> (24 - i * 8)) & 0x000000ff;
		hash[i + 28] = (ctx1->state[7] >> (24 - i * 8)) & 0x000000ff;

	}
}
#pragma endregion

#pragma region SHA256 with approximate KSA32(K=16) adder
// SHA256 with approximate KSA32(K=16) adder
void sha256_transformBKA32N16(SHA256_CTX2* ctx2, const BYTE data[]) // with CLA adder
{

	// original
	//WORD t1, t2,a;

	WORD b, c, d, e, f, g, h, i, j, m[64];
	// edited
	WORD L1, L11, L2, L22, a1, a0;
	//expander adders
	WORD inp1, inp2, inp3, inp11, inp22, inp33;
	WORD sum1, cout1, sum2, cout2, CPAexpout;

	//compressor adders
	//path 1
	WORD csa1, csa2, csa3, csa11, csa22, csa33, csa111, csa222, csa333, csa1111, csa2222, csa3333;
	WORD csasum1, csacout1, csasum2, csacout2, csasum3, csacout3, csasum4, csacout4;
	//path 2
	WORD csaa1, csaa2, csaa3, csaa11, csaa22, csaa33, csaa111, csaa222, csaa333, csaa1111, csaa2222, csaa3333;
	WORD csaasum1, csaacout1, csaasum2, csaacout2, csaasum3, csaacout3, csaasum4, csaacout4;
	WORD CPAcomp1, CPAcomp2;

	for (i = 0, j = 0; i < 16; ++i, j += 4)
		m[i] = (data[j] << 24) | (data[j + 1] << 16) | (data[j + 2] << 8) | (data[j + 3]);

	for (; i < 64; ++i)
	{

		// CSA 1
		inp1 = m[i - 7];
		inp2 = SIG0(m[i - 15]);
		inp3 = m[i - 16];
		// Calculating value of CSA 1sum
		sum1 = CSAsum(inp1, inp2, inp3);
		//Calculating value of CSA 1 C-Out
		cout1 = CSAcout(inp1, inp2, inp3);

		// CSA 2
		inp11 = SIG1(m[i - 2]);
		inp22 = sum1;
		inp33 = cout1;
		// Calculating value of CSA 2 sum
		sum2 = CSAsum(inp11, inp22, inp33);
		//Calculating value of CSA 2 C-Out
		cout2 = CSAcout(inp11, inp22, inp33);

		// 2) KSA32 exp
		// Calculating value of KSA32 output
		CPAexpout = BKA32N16(sum2, cout2);

		// Edited SHA256
		m[i] = CPAexpout;
	}

	a0 = ctx2->a0[0];
	a1 = ctx2->state[0];
	b = ctx2->state[1];
	c = ctx2->state[2];
	d = ctx2->state[3];
	e = ctx2->state[4];
	f = ctx2->state[5];
	g = ctx2->state[6];
	h = ctx2->state[7];

	L1 = 0;
	L11 = 0;
	L2 = 0;
	L22 = 0;

	for (i = 0;i < 1; ++i)
	{
		// Path 1
		// CSA 1 & mux
		csa1 = h;

		csa2 = k[i];

		csa3 = m[i];

		// Calculating value of CSA 1sum
		csasum1 = CSAsum(csa1, csa2, csa3);
		//Calculating value of CSA 1 C-Out
		csacout1 = CSAcout(csa1, csa2, csa3);

		// CSA 2 & mux
		csa11 = d;
		csa22 = csasum1;
		csa33 = csacout1;
		// Calculating value of CSA 2 sum
		csasum2 = CSAsum(csa11, csa22, csa33);
		//Calculating value of CSA 2 C-Out
		csacout2 = CSAcout(csa11, csa22, csa33);

		// CSA 3 & L0
		csa111 = CH(e, f, g);
		csa222 = L1;
		csa333 = L11;
		// Calculating value of CSA 2 sum
		csasum3 = CSAsum(csa111, csa222, csa333);
		//Calculating value of CSA 2 C-Out
		csacout3 = CSAcout(csa111, csa222, csa333);

		// CSA 4
		csa1111 = EP1(e);
		csa2222 = csasum3;
		csa3333 = csacout3;
		// Calculating value of CSA 2 sum
		csasum4 = CSAsum(csa1111, csa2222, csa3333);
		//Calculating value of CSA 2 C-Out
		csacout4 = CSAcout(csa1111, csa2222, csa3333);

		// KSA32 comp 1
		// Calculating value of KSA32 output
		CPAcomp1 = BKA32N16(csasum4, csacout4);




		//path 2
		// need to declare CPAcomp2 first
		/// CPA comp 2
		// Calculating value of KSA32 output
		CPAcomp2 = BKA32N16(a1, a0);

		// CSA 1 & L1
		csaa1 = CH(e, f, g);
		csaa2 = L2;
		csaa3 = L22;
		// Calculating value of CSA 1sum
		csaasum1 = CSAsum(csaa1, csaa2, csaa3);
		//Calculating value of CSA 1 C-Out
		csaacout1 = CSAcout(csaa1, csaa2, csaa3);

		// CSA 2
		csaa11 = EP1(e);
		csaa22 = csaasum1;
		csaa33 = csaacout1;
		// Calculating value of CSA 2 sum
		csaasum2 = CSAsum(csaa11, csaa22, csaa33);
		//Calculating value of CSA 2 C-Out
		csaacout2 = CSAcout(csaa11, csaa22, csaa33);

		// CSA 3 
		csaa111 = MAJ(CPAcomp2, b, c);
		csaa222 = csaasum2;
		csaa333 = csaacout2;
		// Calculating value of CSA 2 sum
		csaasum3 = CSAsum(csaa111, csaa222, csaa333);
		//Calculating value of CSA 2 C-Out
		csaacout3 = CSAcout(csaa111, csaa222, csaa333);

		// CSA 4
		csaa1111 = EP0(CPAcomp2);
		csaa2222 = csaasum3;
		csaa3333 = csaacout3;
		// Calculating value of CSA 2 sum
		csaasum4 = CSAsum(csaa1111, csaa2222, csaa3333);
		//Calculating value of CSA 2 C-Out
		csaacout4 = CSAcout(csaa1111, csaa2222, csaa3333);

		h = h;
		g = g;
		f = f;
		e = e;

		d = d;
		c = c;
		b = b;
		a1 = a1;
		a0 = a0;

		L1 = csasum2;
		L11 = csacout2;

		L2 = csasum1;
		L22 = csacout1;
	}

	for (; i < 2; ++i)
	{
		// Path 1
	// CSA 1 & mux
		csa1 = g;

		csa2 = k[i];

		csa3 = m[i];

		// Calculating value of CSA 1sum
		csasum1 = CSAsum(csa1, csa2, csa3);
		//Calculating value of CSA 1 C-Out
		csacout1 = CSAcout(csa1, csa2, csa3);

		// CSA 2 & mux
		csa11 = c;
		csa22 = csasum1;
		csa33 = csacout1;
		// Calculating value of CSA 2 sum
		csasum2 = CSAsum(csa11, csa22, csa33);
		//Calculating value of CSA 2 C-Out
		csacout2 = CSAcout(csa11, csa22, csa33);

		// CSA 3 & L0
		csa111 = CH(e, f, g);
		csa222 = L1;
		csa333 = L11;
		// Calculating value of CSA 2 sum
		csasum3 = CSAsum(csa111, csa222, csa333);
		//Calculating value of CSA 2 C-Out
		csacout3 = CSAcout(csa111, csa222, csa333);

		// CSA 4
		csa1111 = EP1(e);
		csa2222 = csasum3;
		csa3333 = csacout3;
		// Calculating value of CSA 2 sum
		csasum4 = CSAsum(csa1111, csa2222, csa3333);
		//Calculating value of CSA 2 C-Out
		csacout4 = CSAcout(csa1111, csa2222, csa3333);

		// CPA comp 1
		// Calculating value of KSA32 output
		CPAcomp1 = BKA32N16(csasum4, csacout4);




		//path 2
		// need to declare CPAcomp2 first
		/// KSA32 comp 2
		// Calculating value of KSA32 output
		CPAcomp2 = BKA32N16(a1, a0);

		// CSA 1 & L1
		csaa1 = CH(e, f, g);
		csaa2 = L2;
		csaa3 = L22;
		// Calculating value of CSA 1sum
		csaasum1 = CSAsum(csaa1, csaa2, csaa3);
		//Calculating value of CSA 1 C-Out
		csaacout1 = CSAcout(csaa1, csaa2, csaa3);

		// CSA 2
		csaa11 = EP1(e);
		csaa22 = csaasum1;
		csaa33 = csaacout1;
		// Calculating value of CSA 2 sum
		csaasum2 = CSAsum(csaa11, csaa22, csaa33);
		//Calculating value of CSA 2 C-Out
		csaacout2 = CSAcout(csaa11, csaa22, csaa33);

		// CSA 3 
		csaa111 = MAJ(CPAcomp2, b, c);
		csaa222 = csaasum2;
		csaa333 = csaacout2;
		// Calculating value of CSA 2 sum
		csaasum3 = CSAsum(csaa111, csaa222, csaa333);
		//Calculating value of CSA 2 C-Out
		csaacout3 = CSAcout(csaa111, csaa222, csaa333);

		// CSA 4
		csaa1111 = EP0(CPAcomp2);
		csaa2222 = csaasum3;
		csaa3333 = csaacout3;
		// Calculating value of CSA 2 sum
		csaasum4 = CSAsum(csaa1111, csaa2222, csaa3333);
		//Calculating value of CSA 2 C-Out
		csaacout4 = CSAcout(csaa1111, csaa2222, csaa3333);

		h = g;
		g = f;
		f = e;
		e = CPAcomp1;

		d = c;
		c = b;
		b = CPAcomp2;
		a1 = csaasum4;
		a0 = csaacout4;

		L1 = csasum2;
		L11 = csacout2;

		L2 = csasum1;
		L22 = csacout1;
	}

	for (; i < 64; ++i)
	{
		// Path 1
		// CSA 1 & mux
		csa1 = g;

		csa2 = k[i];

		csa3 = m[i];

		// Calculating value of CSA 1sum
		csasum1 = CSAsum(csa1, csa2, csa3);
		//Calculating value of CSA 1 C-Out
		csacout1 = CSAcout(csa1, csa2, csa3);

		// CSA 2 & mux
		csa11 = c;
		csa22 = csasum1;
		csa33 = csacout1;
		// Calculating value of CSA 2 sum
		csasum2 = CSAsum(csa11, csa22, csa33);
		//Calculating value of CSA 2 C-Out
		csacout2 = CSAcout(csa11, csa22, csa33);

		// CSA 3 & L0
		csa111 = CH(e, f, g);
		csa222 = L1;
		csa333 = L11;
		// Calculating value of CSA 2 sum
		csasum3 = CSAsum(csa111, csa222, csa333);
		//Calculating value of CSA 2 C-Out
		csacout3 = CSAcout(csa111, csa222, csa333);

		// CSA 4
		csa1111 = EP1(e);
		csa2222 = csasum3;
		csa3333 = csacout3;
		// Calculating value of CSA 2 sum
		csasum4 = CSAsum(csa1111, csa2222, csa3333);
		//Calculating value of CSA 2 C-Out
		csacout4 = CSAcout(csa1111, csa2222, csa3333);

		// CPA comp 1
		// Calculating value of KSA32 output
		CPAcomp1 = BKA32N16(csasum4, csacout4);




		//path 2
		// need to declare CPAcomp2 first
		/// KSA32 comp 2
		// Calculating value of KSA32 output
		CPAcomp2 = BKA32N16(a1, a0);

		// CSA 1 & L1
		csaa1 = CH(e, f, g);
		csaa2 = L2;
		csaa3 = L22;
		// Calculating value of CSA 1sum
		csaasum1 = CSAsum(csaa1, csaa2, csaa3);
		//Calculating value of CSA 1 C-Out
		csaacout1 = CSAcout(csaa1, csaa2, csaa3);

		// CSA 2
		csaa11 = EP1(e);
		csaa22 = csaasum1;
		csaa33 = csaacout1;
		// Calculating value of CSA 2 sum
		csaasum2 = CSAsum(csaa11, csaa22, csaa33);
		//Calculating value of CSA 2 C-Out
		csaacout2 = CSAcout(csaa11, csaa22, csaa33);

		// CSA 3 
		csaa111 = MAJ(CPAcomp2, b, c);
		csaa222 = csaasum2;
		csaa333 = csaacout2;
		// Calculating value of CSA 2 sum
		csaasum3 = CSAsum(csaa111, csaa222, csaa333);
		//Calculating value of CSA 2 C-Out
		csaacout3 = CSAcout(csaa111, csaa222, csaa333);

		// CSA 4
		csaa1111 = EP0(CPAcomp2);
		csaa2222 = csaasum3;
		csaa3333 = csaacout3;
		// Calculating value of CSA 2 sum
		csaasum4 = CSAsum(csaa1111, csaa2222, csaa3333);
		//Calculating value of CSA 2 C-Out
		csaacout4 = CSAcout(csaa1111, csaa2222, csaa3333);

		h = g;
		g = f;
		f = e;
		e = CPAcomp1;

		d = c;
		c = b;
		b = CPAcomp2;
		a1 = csaasum4;
		a0 = csaacout4;

		L1 = csasum2;
		L11 = csacout2;

		L2 = csasum1;
		L22 = csacout1;
	}

	for (; i < 65; ++i)
	{
		// Path 1
		// CSA 1 & mux
		csa1 = g;

		csa2 = k[i];

		csa3 = m[i];

		//workable
		//csa3 = m[i];

		// Calculating value of CSA 1sum
		csasum1 = CSAsum(csa1, csa2, csa3);
		//Calculating value of CSA 1 C-Out
		csacout1 = CSAcout(csa1, csa2, csa3);

		// CSA 2 & mux
		csa11 = c;
		csa22 = csasum1;
		csa33 = csacout1;
		// Calculating value of CSA 2 sum
		csasum2 = CSAsum(csa11, csa22, csa33);
		//Calculating value of CSA 2 C-Out
		csacout2 = CSAcout(csa11, csa22, csa33);

		// CSA 3 & L0
		csa111 = CH(e, f, g);
		csa222 = L1;
		csa333 = L11;
		// Calculating value of CSA 2 sum
		csasum3 = CSAsum(csa111, csa222, csa333);
		//Calculating value of CSA 2 C-Out
		csacout3 = CSAcout(csa111, csa222, csa333);

		// CSA 4
		csa1111 = EP1(e);
		csa2222 = csasum3;
		csa3333 = csacout3;
		// Calculating value of CSA 2 sum
		csasum4 = CSAsum(csa1111, csa2222, csa3333);
		//Calculating value of CSA 2 C-Out
		csacout4 = CSAcout(csa1111, csa2222, csa3333);

		// CPA comp 1
		// Calculating value of KSA32 output
		CPAcomp1 = BKA32N16(csasum4, csacout4);


		//path 2
		// need to declare CPAcomp2 first
		/// KSA32 comp 2
		// Calculating value of KSA32 output
		CPAcomp2 = BKA32N16(a1, a0);

		// CSA 1 & L1
		csaa1 = CH(e, f, g);
		csaa2 = L2;
		csaa3 = L22;
		// Calculating value of CSA 1sum
		csaasum1 = CSAsum(csaa1, csaa2, csaa3);
		//Calculating value of CSA 1 C-Out
		csaacout1 = CSAcout(csaa1, csaa2, csaa3);

		// CSA 2
		csaa11 = EP1(e);
		csaa22 = csaasum1;
		csaa33 = csaacout1;
		// Calculating value of CSA 2 sum
		csaasum2 = CSAsum(csaa11, csaa22, csaa33);
		//Calculating value of CSA 2 C-Out
		csaacout2 = CSAcout(csaa11, csaa22, csaa33);

		// CSA 3 
		csaa111 = MAJ(CPAcomp2, b, c);
		csaa222 = csaasum2;
		csaa333 = csaacout2;
		// Calculating value of CSA 2 sum
		csaasum3 = CSAsum(csaa111, csaa222, csaa333);
		//Calculating value of CSA 2 C-Out
		csaacout3 = CSAcout(csaa111, csaa222, csaa333);

		// CSA 4
		csaa1111 = EP0(CPAcomp2);
		csaa2222 = csaasum3;
		csaa3333 = csaacout3;
		// Calculating value of CSA 2 sum
		csaasum4 = CSAsum(csaa1111, csaa2222, csaa3333);
		//Calculating value of CSA 2 C-Out
		csaacout4 = CSAcout(csaa1111, csaa2222, csaa3333);

		h = g;
		g = f;
		f = e;
		e = CPAcomp1;

		d = c;
		c = b;
		b = CPAcomp2;
		a1 = csaasum4;
		a0 = csaacout4;
		a1 = BKA32N16(a1, a0);
		a0 = 0;


		L1 = csasum2;
		L11 = csacout2;

		L2 = csasum1;
		L22 = csacout1;
	}

	ctx2->a0[0] += a0;
	ctx2->state[0] += a1;
	ctx2->state[1] += b;
	ctx2->state[2] += c;
	ctx2->state[3] += d;
	ctx2->state[4] += e;
	ctx2->state[5] += f;
	ctx2->state[6] += g;
	ctx2->state[7] += h;
}
void sha256_initBKA32N16(SHA256_CTX2* ctx2)
{
	ctx2->datalen = 0;
	ctx2->bitlen = 0;

	ctx2->a0[0] = 0x00000000;
	ctx2->state[0] = 0x6a09e667;
	ctx2->state[1] = 0xbb67ae85;
	ctx2->state[2] = 0x3c6ef372;
	ctx2->state[3] = 0xa54ff53a;
	ctx2->state[4] = 0x510e527f;
	ctx2->state[5] = 0x9b05688c;
	ctx2->state[6] = 0x1f83d9ab;
	ctx2->state[7] = 0x5be0cd19;
}
void sha256_updateBKA32N16(SHA256_CTX2* ctx2, const BYTE data[], size_t len)
{
	WORD i;

	for (i = 0; i < len; ++i) {
		ctx2->data[ctx2->datalen] = data[i];
		ctx2->datalen++;
		if (ctx2->datalen == 64) {
			sha256_transformBKA32N16(ctx2, ctx2->data);
			ctx2->bitlen += 512;
			ctx2->datalen = 0;
		}
	}
}
void sha256_finalBKA32N16(SHA256_CTX2* ctx2, BYTE hash[])
{
	WORD i;

	i = ctx2->datalen;

	// Pad whatever data is left in the buffer.
	if (ctx2->datalen < 56) {
		ctx2->data[i++] = 0x80;
		while (i < 56)
			ctx2->data[i++] = 0x00;
	}
	else {
		ctx2->data[i++] = 0x80;
		while (i < 64)
			ctx2->data[i++] = 0x00;
		sha256_transformBKA32N16(ctx2, ctx2->data);
		memset(ctx2->data, 0, 56);
	}

	// Append to the padding the total message's length in bits and transform.
	ctx2->bitlen += ctx2->datalen * 8;
	ctx2->data[63] = ctx2->bitlen;
	ctx2->data[62] = ctx2->bitlen >> 8;
	ctx2->data[61] = ctx2->bitlen >> 16;
	ctx2->data[60] = ctx2->bitlen >> 24;
	ctx2->data[59] = ctx2->bitlen >> 32;
	ctx2->data[58] = ctx2->bitlen >> 40;
	ctx2->data[57] = ctx2->bitlen >> 48;
	ctx2->data[56] = ctx2->bitlen >> 56;
	sha256_transformBKA32N16(ctx2, ctx2->data);

	// Since this implementation uses little endian byte ordering and SHA uses big endian,
	// reverse all the bytes when copying the final state to the output hash.
	for (i = 0; i < 4; ++i) {

		hash[i] = (ctx2->state[0] >> (24 - i * 8)) & 0x000000ff;
		hash[i + 4] = (ctx2->state[1] >> (24 - i * 8)) & 0x000000ff;
		hash[i + 8] = (ctx2->state[2] >> (24 - i * 8)) & 0x000000ff;
		hash[i + 12] = (ctx2->state[3] >> (24 - i * 8)) & 0x000000ff;
		hash[i + 16] = (ctx2->state[4] >> (24 - i * 8)) & 0x000000ff;
		hash[i + 20] = (ctx2->state[5] >> (24 - i * 8)) & 0x000000ff;
		hash[i + 24] = (ctx2->state[6] >> (24 - i * 8)) & 0x000000ff;
		hash[i + 28] = (ctx2->state[7] >> (24 - i * 8)) & 0x000000ff;

	}
}
#pragma endregion

//Method to convert hexadecimal output to binary

void convert(string str, FILE* fp)
{
	int i = 0;
	while (str[i])
	{
		switch (str[i])
		{
		case '0':
			//printf("0000");
			fprintf(fp, "0000");
			break;
		case '1':
			//printf("0001");
			fprintf(fp, "0001");
			break;
		case '2':
			//printf("0010");
			fprintf(fp, "0010");
			break;
		case '3':
			//printf("0011");
			fprintf(fp, "0011");
			break;
		case '4':
			//printf("0100");
			fprintf(fp, "0100");
			break;
		case '5':
			//printf("0101");
			fprintf(fp, "0101");
			break;
		case '6':
			//printf("0110");
			fprintf(fp, "0110");
			break;
		case '7':
			//printf("0111");
			fprintf(fp, "0111");
			break;
		case '8':
			//printf("1000");
			fprintf(fp, "1000");
			break;
		case '9':
			//printf("1001");
			fprintf(fp, "1001");
			break;
		case 'A':
		case 'a':
			//printf("1010");
			fprintf(fp, "1010");
			break;
		case 'B':
		case 'b':
			//printf("1011");
			fprintf(fp, "1011");
			break;
		case 'C':
		case 'c':
			//printf("1100");
			fprintf(fp, "1100");
			break;
		case 'D':
		case 'd':
			//printf("1101");
			fprintf(fp, "1101");
			break;
		case 'E':
		case 'e':
			//printf("1110");
			fprintf(fp, "1110");
			break;
		case 'F':
		case 'f':
			//printf("1111");
			fprintf(fp, "1111");
			break;
		default:
			//printf("\please enter valid hexadecimal digit ");
			fprintf(fp, "please enter valid hexadecimal digit");
		}
		i++;
	}
}

//Main Program

#pragma region Main Program
// Main 
int main()
{
	// Declare variables
	BYTE buf[SHA256_BLOCK_SIZE];
	BYTE buf1[SHA256_BLOCK_SIZE];
	BYTE buf2[SHA256_BLOCK_SIZE];
	SHA256_CTX ctx;
	SHA256_CTX1 ctx1;
	SHA256_CTX2 ctx2;
	
	int i;
	float pass1 = 0, pass2 = 0;
	float fail1 = 0, fail2 = 0;
	float error1, error2;
	float simulation = 0;

	// Seed number for rand()
	srand((unsigned int)time(0) + _getpid());

	//Hexadecimal Hash Files
	FILE* fp; //File for non approximate KSA32 Hashes in hexadecimal
	FILE* fp1; //File for approximate KSA32 K=8 Hashes in hexadecimal
	FILE* fp2; //File for approximate KSA32 K=16 Hashes in hexadecimal
	
	fopen_s(&fp, "C:\\Users\\Cameron\\source\\repos\\My Project Code\\BKA\\KSA\\HashOutputFiles\\NonApproxBKAHashFile.txt", "w+"); //Open file for non approximate KSA32 Hashes
	fopen_s(&fp1, "C:\\Users\\Cameron\\source\\repos\\My Project Code\\BKA\\KSA\\HashOutputFiles\\ApproxBKAK8HashFile.txt", "w+"); //Open file for approximate KSA32 K=8 Hashes
	fopen_s(&fp2, "C:\\Users\\Cameron\\source\\repos\\My Project Code\\BKA\\KSA\\HashOutputFiles\\ApproxBKAK16HashFile.txt", "w+"); //Open file for approximate KSA32 K=16 Hashes

	//Binary Hash Files
	FILE* fp3; //File for non approximate KSA32 Hashes in binary format
	FILE* fp4; //File for approximate KSA32 K=8 Hashes in binary format
	FILE* fp5; //File for approximate KSA32 K=16 Hasesh in binary format
	
	fopen_s(&fp3, "C:\\Users\\Cameron\\source\\repos\\My Project Code\\BKA\\KSA\\BinaryHashOuputFiles\\NonApproxBKAHashBinaryFile.txt", "w + "); //Open file for non approximate KSA32 Hashes in binary format
	fopen_s(&fp4, "C:\\Users\\Cameron\\source\\repos\\My Project Code\\BKA\\KSA\\BinaryHashOuputFiles\\ApproxBKAK8HashBinaryFile.txt", "w + "); //Open file for non approximate KSA32 Hashes in binary format
	fopen_s(&fp5, "C:\\Users\\Cameron\\source\\repos\\My Project Code\\BKA\\KSA\\BinaryHashOuputFiles\\ApproxBKAK16HashBinaryFile.txt", "w + "); //Open file for non approximate KSA32 Hashes in binary format

	if (fp == NULL) //Check if the file is null
	{
		printf("file can't be opened\n");
		exit(1);
	}

	if (fp1 == NULL) //Check if the file is null
	{
		printf("file can't be opened\n");
		exit(1);
	}

	if (fp2 == NULL) //Check if the file is null
	{
		printf("file can't be opened\n");
		exit(1);
	}

	fflush(stdin);

	// Run the simulation 10000 times
	for (i = 0; i < 1000; i++)
	{

		int test1 = 1;
		int test2 = 1;
		int length = 32;
		int j = 0;

		int s = 0;
		int x = 0;
		int y = 0;

		BYTE str[] = "0123456789ABCDEFabcdef";
		BYTE SHA256_input[64] = { "\0" }; //declaring an empty string

		//create Random input for current run
		for (j = 0; j < length; j++)
		{
			SHA256_input[j] = str[rand() % 22];
		}

		// -------------------------
		// What is observed here, are the input hashes being hashed again (as is custom within the bitcoin network) using a variety of different schemes.
		// These are as follows: Non approximate KSA32, Approximate KSA32(K=8) and Approximate KSA32(K=16).
		// The output hashes from these schemes can be verified to be correct using an online SHA256 encoder/decoder.

		// What now must be done for my project is to obtain all 1000 simulations of each of the hash outputs from these schemes, and place these within a file to 
		// Be further analysed within the NIST test suite.
		// End of Work Area
		
		// See hash inputs
		printf("\n");
		printf("-----------------------------------------------------------------------------------");
		printf("\n");
		printf("--------------------------------- N E W  H A S H ----------------------------------");
		printf("\n");
		printf("-----------------------------------------------------------------------------------");
		printf("\n");
		printf("Actual Input Hash which is passed into SHA256 functions: ");
		for (j = 0; j < SHA256_BLOCK_SIZE; j++)
		{
			printf("%c", SHA256_input[j]);
		}
		printf("\n");

		// SHA256 with non approximate BKA32 
		sha256_init(&ctx);
		sha256_update(&ctx, (const BYTE*)SHA256_input, strlen((const char*)SHA256_input));
		sha256_final(&ctx, buf);

		//Print a hash from non approximate BKA
		printf("Actual hash from non approximate BKA: ");
		for (s = 0; s < SHA256_BLOCK_SIZE; s++)
		{
			printf("%02x", buf[s]); //Print on Console App
			fprintf(fp, "%02x", buf[s]); //Write to text file
				
		}
		fprintf(fp, "\n"); //New Line in text file
		printf("\n"); //New Line on Console Application

		printf("Binary Output for non approximate BKA hash: ");
		for (s = 0; s < SHA256_BLOCK_SIZE; s++)
		{
			char n[4];
			snprintf(n, 4, "%02X", buf[s]);
			string str(n);
			convert(str, fp3);
		}
		fprintf(fp3, "\n"); //New Line in text file
		printf("\n"); //New Line on Console Application

		//sha256 with approximate KSA32(K=8)
		sha256_initBKA32N8(&ctx1);
		sha256_updateBKA32N8(&ctx1, (const BYTE*)SHA256_input, strlen((const char*)SHA256_input));
		sha256_finalBKA32N8(&ctx1, buf1);

		//Print a hash from approximate KSA32(K=8)
		printf("Hash from approximate BKA32(K=8): ");
		for (x = 0; x < SHA256_BLOCK_SIZE; x++)
		{
			printf("%02x", buf1[x]); //Print on Console App
			fprintf(fp1, "%02x", buf1[x]); //Write to text file
		}
		fprintf(fp1, "\n"); //New Line in text file
		printf("\n"); //New Line on Console Application

		printf("Binary Output for  approximate BKA32(K=8) hash: ");
		for (x = 0; x < SHA256_BLOCK_SIZE; x++)
		{
			char n[4];
			snprintf(n, 4, "%02X", buf1[x]);
			string str(n);
			convert(str, fp4);
		}
		fprintf(fp4, "\n"); //New Line in text file
		printf("\n"); //New Line on Console Application

		//sha256 with approximate KSA32(K=16)
		sha256_initBKA32N16(&ctx2);
		sha256_updateBKA32N16(&ctx2, (const BYTE*)SHA256_input, strlen((const char*)SHA256_input));
		sha256_finalBKA32N16(&ctx2, buf2);

		//Print a hash from approximate KSA32(K=16)
		printf("Hash from approximate BKA32(K=16): ");
		for (y = 0; y < SHA256_BLOCK_SIZE; y++)
		{
			//printf("BKA32N16 Hash:");
			printf("%02x", buf2[y]); //Print on Console App
			fprintf(fp2, "%02x", buf2[y]); //Write to text file
		}
		fprintf(fp2, "\n"); //New Line in text file
		printf("\n"); //New Line on Console Application

		printf("Binary Output for  approximate BKA32(K=16) hash: ");
		for (y = 0; y < SHA256_BLOCK_SIZE; y++)
		{
			char n[4];
			snprintf(n, 4, "%02X", buf2[y]);
			string str(n);
			convert(str, fp5);
		}
		fprintf(fp5, "\n"); //New Line in text file
		printf("\n"); //New Line on Console Application

		//Tests
		test1 = test1 && !memcmp(buf, buf1, SHA256_BLOCK_SIZE); //Comparing memory buffer of hashes from non-approx KSA and approximate KSA(K=8)

		if (test1 == 1)
		{
			pass1 = pass1 + 1;
			printf("\n");
			printf(" - Non Approximate BKA Hash SUCCESSFULLY Matches Approximate BKA(K=8) Hash!");
			printf("\n");
		}
		else
		{
			fail1 = fail1 + 1;
			printf("\n");
			printf(" - Non Approximate BKA Hash DOES NOT Match Approximate BKA(K=8) Hash!");
			printf("\n");
		}

		test2 = test2 && !memcmp(buf, buf2, SHA256_BLOCK_SIZE); //Comparing memory buffer of hashes from non-approx KSA and approximate KSA(K=16)

		if (test2 == 1)
		{
			pass2 = pass2 + 1;
			printf("\n");
			printf(" - Non Approximate BKA Hash SUCCESSFULLY Matches Approximate BKA(K=16) Hash!");
			printf("\n");
		}
		else
		{
			fail2 = fail2 + 1;
			printf("\n");
			printf(" - Non Approximate BKA Hash DOES NOT Match Approximate BKA(K=16) Hash!");
			printf("\n");
		}
		printf("\n");
		printf("***********************************************************************************");
		printf("\n");
		simulation++;
	}
	//Error rate
	error1 = (fail1 / (pass1 + fail1));
	error2 = (fail2 / (pass2 + fail2));

	// Display results and profit
	// Profit calculation
	// SHA256 with KSA32 adder
	float k0cost = electricity(0);
	float k0revenue = totalrevenue(0, k0cost);
	float k0profit = totalprofit(k0revenue, k0cost);

	printf("-----------------------------------------------------------------------------------");
	printf("\n");
	printf("------------------------ E X P E R I M E N T  R E S U L T S -----------------------");
	printf("\n");
	printf("-----------------------------------------------------------------------------------");
	printf("\n");
	printf("SHA256 with non-approximate BKA32 adder profit & cost \n");
	printf("Revenue: %.3f \n", k0revenue);
	printf("Electricity cost: %.3f \n", k0cost);
	printf("Profit: %.3f \n\n\n\n", k0profit);


	// KSA32 against approximate KSA32(k=16)
	printf("Compare SHA256 output(Normal BKA32 adder against approximate BKA32(k=16) adder\n");
	printf("Simulation: %.f times\n", simulation);
	printf("Passed: %.f\n", pass2);
	printf("Failed: %.f\n", fail2);
	printf("Error rate: %.3f percent\n\n", (error2 * 100));

	// Profit calculation
	// SHA256 with approximate KSA32(k=16) adder
	float k16cost = electricity(error2);
	float k16revenue = totalrevenue(error2, k16cost);
	float k16profit = totalprofit(k16revenue, k16cost);
	float k16profitgain = ((k16profit / k0profit) - 1) * 100;
	printf("SHA256 with approximate BKA32(k=16) adder profit & cost \n");
	printf("Revenue: %.3f \n", k16revenue);
	printf("Electricity cost: %.3f \n", k16cost);
	printf("Profit: %.3f \n", k16profit);
	printf("Profit gain against non-approximate SHA256: %.3f percent \n\n\n\n", k16profitgain);


	// KSA32 against approximate KSA32(k=8) 
	printf("Compare SHA256 output(Normal BKA32 adder against approximate BKA32(k=8) adder\n");
	printf("Simulation: %.f times\n", simulation);
	printf("Passed: %.f\n", pass1);
	printf("Failed: %.f\n", fail1);
	printf("Error rate: %.3f percent\n\n", (error1 * 100));

	// Profit calculation
	// SHA256 with approximate KSA32(k=8) adder
	float k8cost = electricity(error1);
	float k8revenue = totalrevenue(error1, k8cost);
	float k8profit = totalprofit(k8revenue, k8cost);
	float k8profitgain = ((k8profit / k0profit) - 1) * 100;
	printf("SHA256 with approximate BK32(k=8) adder profit & cost \n");
	printf("Revenue: %.3f \n", k8revenue);
	printf("Electricity cost: %.3f \n", k8cost);
	printf("Profit: %.3f \n", k8profit);
	printf("Profit gain against non-approximate SHA256: %.3f percent \n\n\n\n", k8profitgain);
	return(0);

}

// Run program: Ctrl + F5 or Debug > Start Without Debugging menu
// Debug program: F5 or Debug > Start Debugging menu

// Tips for Getting Started: 
//   1. Use the Solution Explorer window to add/manage files
//   2. Use the Team Explorer window to connect to source control
//   3. Use the Output window to see build output and other messages
//   4. Use the Error List window to view errors
//   5. Go to Project > Add New Item to create new code files, or Project > Add Existing Item to add existing code files to the project
//   6. In the future, to open this project again, go to File > Open > Project and select the .sln file

#pragma endregion