#include "sha2.h"

#include <cstring>
#include <iomanip>
#include <iostream>
#include <sstream>

using namespace std;

namespace xamidi {
namespace cryptography {

// SHA-2 validation sample

void sha2_sample() {
	auto check = [](const string& correct, const string& result) {
		cout << "Hash: " << result << endl;
		if (correct != result) {
			cout << "Test failed, expected " << correct << "." << endl;
			return false;
		}
		return true;
	};
	string correctHashes[6][3] =
	{	// SHA-224
		{ "8552d8b7a7dc5476cb9e25dee69a8091290764b7f2a64fe6e78e9568",
		  "d40854fc9caf172067136f2e29e1380b14626bf6f0dd06779f820dcd",
		  "20794655980c91d8bbb4c1ea97618a4bf03f42581948b2ee4ee7ad67" },
		// SHA-256
		{ "315f5bdb76d078c43b8ac0064e4a0164612b1fce77c869345bfc94c75894edd3",
		  "b35439a4ac6f0948b6d6f9e3c6af0f5f590ce20f1bde7090ef7970686ec6738a",
		  "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0" },
		// SHA-384
		{ "55bc556b0d2fe0fce582ba5fe07baafff035653638c7ac0d5494c2a64c0bea1cc57331c7c12a45cdbca7f4c34a089eeb",
		  "e6f8fc9807cf07d835566f50978d72022b2d718f5b0b75a4594187c73487c0baedf4e289b340428164e42938f54abcfb",
		  "9d0e1809716474cb086e834e310a4a1ced149e9c00f248527972cec5704c2a5b07b8b3dc38ecc4ebae97ddd87f3d8985" },
		// SHA-512
		{ "c1527cd893c124773d811911970c8fe6e857d6df5dc9226bd8a160614c0cd963a4ddea2b94bb7d36021ef9d865d5cea294a82dd49a0bb269f51f6e7a57f79421",
		  "39ba3c74b23cb7deffb5d59624e320c08692637057daaaeea4d847e1d3b6a2ce6895ff3c609d57da490484b030ed231d5bdfafcfe264bd3d91cddb39c2d036ab",
		  "e718483d0ce769644e2e42c7bc15b4638e1f98b13b2044285632a803afa973ebde0ff244877ea60a4cb0432ce577c31beb009c5c2c49aa2e4eadb217ad8cc09b" },
		// SHA-512/224
		{ "32620068b859669b45b31008e08b7384649ad2ca3f5163a3a71e5745",
		  "d8f99e6da8fabb2df01c48a3b46d15105637bae546b98dc17ad292fd",
		  "37ab331d76f0d36de422bd0edeb22a28accd487b7a8453ae965dd287" },
		// SHA-512/256
		{ "330c723f25267587db0b9f493463e017011239169cb57a6db216c63774367115",
		  "cf816c408ac0fa52343249864bf0227dd4d9be6794f7f7de2c15160707c8dc05",
		  "9a59a052930187a97038cae692f30708aa6491923ef5194394dc68d56c74fb21" }
	};
	string msg1 = "Hello, world!";
	string msg2a(56, 'a');
	string msg2b(96, 'a');
	string msg3(1000000, 'a');
	bool success = true;

	cout << "SHA-224" << endl;
	success &= check(correctHashes[0][0], sha224(msg1));
	success &= check(correctHashes[0][1], sha224(msg2a));
	success &= check(correctHashes[0][2], sha224(msg3));
	cout << endl;

	cout << "SHA-256" << endl;
	success &= check(correctHashes[1][0], sha256(msg1));
	success &= check(correctHashes[1][1], sha256(msg2a));
	success &= check(correctHashes[1][2], sha256(msg3));
	cout << endl;

	cout << "SHA-384" << endl;
	success &= check(correctHashes[2][0], sha384(msg1));
	success &= check(correctHashes[2][1], sha384(msg2b));
	success &= check(correctHashes[2][2], sha384(msg3));
	cout << endl;

	cout << "SHA-512" << endl;
	success &= check(correctHashes[3][0], sha512(msg1));
	success &= check(correctHashes[3][1], sha512(msg2b));
	success &= check(correctHashes[3][2], sha512(msg3));
	cout << endl;

	cout << "SHA-512/224" << endl;
	success &= check(correctHashes[4][0], sha512_224(msg1));
	success &= check(correctHashes[4][1], sha512_224(msg2b));
	success &= check(correctHashes[4][2], sha512_224(msg3));
	cout << endl;

	cout << "SHA-512/256" << endl;
	success &= check(correctHashes[5][0], sha512_256(msg1));
	success &= check(correctHashes[5][1], sha512_256(msg2b));
	success &= check(correctHashes[5][2], sha512_256(msg3));
	cout << endl;

	if (success)
		cout << "All tests passed." << endl;
	else
		cerr << "Some tests failed." << endl;
}

// Initial hash values

uint32_t sha224_h0[8] = {
		0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939,
		0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4 };

uint32_t sha256_h0[8] = {
		0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
		0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 };

uint64_t sha384_h0[8] = {
		0xcbbb9d5dc1059ed8uLL, 0x629a292a367cd507uLL, 0x9159015a3070dd17uLL, 0x152fecd8f70e5939uLL,
		0x67332667ffc00b31uLL, 0x8eb44a8768581511uLL, 0xdb0c2e0d64f98fa7uLL, 0x47b5481dbefa4fa4uLL };

uint64_t sha512_h0[8] = {
		0x6a09e667f3bcc908uLL, 0xbb67ae8584caa73buLL, 0x3c6ef372fe94f82buLL, 0xa54ff53a5f1d36f1uLL,
		0x510e527fade682d1uLL, 0x9b05688c2b3e6c1fuLL, 0x1f83d9abfb41bd6buLL, 0x5be0cd19137e2179uLL };

uint64_t sha512_224_h0[8] = {
		0x8c3d37c819544da2uLL, 0x73e1996689dcd4d6uLL, 0x1dfab7ae32ff9c82uLL, 0x679dd514582f9fcfuLL,
		0x0f6d2b697bd44da8uLL, 0x77e36f7304c48942uLL, 0x3f9d85a86a1d36c8uLL, 0x1112e6ad91d692a1uLL };

uint64_t sha512_256_h0[8] = {
		0x22312194fc2bf72cuLL, 0x9f555fa3c84c64c2uLL, 0x2393b86b6f53b151uLL, 0x963877195940eabduLL,
		0x96283ee2a88effe3uLL, 0xbe5e1e2553863992uLL, 0x2b0199fc2c85b8aauLL, 0x0eb72ddc81c52ca2uLL };

// Initial round constants

uint32_t sha256_k[64] = {
		0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
		0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
		0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
		0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
		0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
		0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
		0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
		0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2 };

uint64_t sha512_k[80] = {
		0x428a2f98d728ae22uLL, 0x7137449123ef65cduLL, 0xb5c0fbcfec4d3b2fuLL, 0xe9b5dba58189dbbcuLL, 0x3956c25bf348b538uLL,
		0x59f111f1b605d019uLL, 0x923f82a4af194f9buLL, 0xab1c5ed5da6d8118uLL, 0xd807aa98a3030242uLL, 0x12835b0145706fbeuLL,
		0x243185be4ee4b28cuLL, 0x550c7dc3d5ffb4e2uLL, 0x72be5d74f27b896fuLL, 0x80deb1fe3b1696b1uLL, 0x9bdc06a725c71235uLL,
		0xc19bf174cf692694uLL, 0xe49b69c19ef14ad2uLL, 0xefbe4786384f25e3uLL, 0x0fc19dc68b8cd5b5uLL, 0x240ca1cc77ac9c65uLL,
		0x2de92c6f592b0275uLL, 0x4a7484aa6ea6e483uLL, 0x5cb0a9dcbd41fbd4uLL, 0x76f988da831153b5uLL, 0x983e5152ee66dfabuLL,
		0xa831c66d2db43210uLL, 0xb00327c898fb213fuLL, 0xbf597fc7beef0ee4uLL, 0xc6e00bf33da88fc2uLL, 0xd5a79147930aa725uLL,
		0x06ca6351e003826fuLL, 0x142929670a0e6e70uLL, 0x27b70a8546d22ffcuLL, 0x2e1b21385c26c926uLL, 0x4d2c6dfc5ac42aeduLL,
		0x53380d139d95b3dfuLL, 0x650a73548baf63deuLL, 0x766a0abb3c77b2a8uLL, 0x81c2c92e47edaee6uLL, 0x92722c851482353buLL,
		0xa2bfe8a14cf10364uLL, 0xa81a664bbc423001uLL, 0xc24b8b70d0f89791uLL, 0xc76c51a30654be30uLL, 0xd192e819d6ef5218uLL,
		0xd69906245565a910uLL, 0xf40e35855771202auLL, 0x106aa07032bbd1b8uLL, 0x19a4c116b8d2d0c8uLL, 0x1e376c085141ab53uLL,
		0x2748774cdf8eeb99uLL, 0x34b0bcb5e19b48a8uLL, 0x391c0cb3c5c95a63uLL, 0x4ed8aa4ae3418acbuLL, 0x5b9cca4f7763e373uLL,
		0x682e6ff3d6b2b8a3uLL, 0x748f82ee5defb2fcuLL, 0x78a5636f43172f60uLL, 0x84c87814a1f0ab72uLL, 0x8cc702081a6439ecuLL,
		0x90befffa23631e28uLL, 0xa4506cebde82bde9uLL, 0xbef9a3f7b2c67915uLL, 0xc67178f2e372532buLL, 0xca273eceea26619cuLL,
		0xd186b8c721c0c207uLL, 0xeada7dd6cde0eb1euLL, 0xf57d4f7fee6ed178uLL, 0x06f067aa72176fbauLL, 0x0a637dc5a2c898a6uLL,
		0x113f9804bef90daeuLL, 0x1b710b35131c471buLL, 0x28db77f523047d84uLL, 0x32caab7b40c72493uLL, 0x3c9ebe0a15c9bebcuLL,
		0x431d67c49c100d4cuLL, 0x4cc5d4becb3e42b6uLL, 0x597f299cfc657e2auLL, 0x5fcb6fab3ad6faecuLL, 0x6c44198c4a475817uLL };

// Hash processing operations

#define CH(x, y, z) (((x) & (y)) ^ (~(x) & (z)))
#define MAJ(x, y, z) (((x) & (y)) ^ ((x) & (z)) ^ ((y) & (z)))
#define ROTR(x, n) (((x) >> (n)) | ((x) << ((sizeof(x) << 3) - (n))))

#define SHA256_S0(x) (ROTR(x, 17) ^ ROTR(x, 19) ^ (x >> 10))
#define SHA256_S1(x) (ROTR(x,  7) ^ ROTR(x, 18) ^ (x >> 3))
#define SHA256_S2(x) (ROTR(x,  6) ^ ROTR(x, 11) ^ ROTR(x, 25))
#define SHA256_S3(x) (ROTR(x,  2) ^ ROTR(x, 13) ^ ROTR(x, 22))

#define SHA512_S0(x) (ROTR(x, 19) ^ ROTR(x, 61) ^ (x >> 6))
#define SHA512_S1(x) (ROTR(x,  1) ^ ROTR(x,  8) ^ (x >> 7))
#define SHA512_S2(x) (ROTR(x, 14) ^ ROTR(x, 18) ^ ROTR(x, 41))
#define SHA512_S3(x) (ROTR(x, 28) ^ ROTR(x, 34) ^ ROTR(x, 39))

void pack32(const unsigned char* str, uint32_t& x) {
	x = ((uint32_t) *(str + 3))
	  | ((uint32_t) *(str + 2) << 8)
	  | ((uint32_t) *(str + 1) << 16)
	  | ((uint32_t) *(str + 0) << 24);
}
void pack64(const unsigned char* str, uint64_t& x) {
	x = ((uint64_t) *(str + 7))
	  | ((uint64_t) *(str + 6) << 8)
	  | ((uint64_t) *(str + 5) << 16)
	  | ((uint64_t) *(str + 4) << 24)
	  | ((uint64_t) *(str + 3) << 32)
	  | ((uint64_t) *(str + 2) << 40)
	  | ((uint64_t) *(str + 1) << 48)
	  | ((uint64_t) *(str + 0) << 56);
}

void unpack32(uint32_t x, unsigned char* str) {
	*(str + 3) = (uint8_t) x;
	*(str + 2) = (uint8_t) (x >> 8);
	*(str + 1) = (uint8_t) (x >> 16);
	*(str + 0) = (uint8_t) (x >> 24);
}
void unpack64(uint64_t x, unsigned char* str) {
	*(str + 7) = (uint8_t) x;
	*(str + 6) = (uint8_t) (x >> 8);
	*(str + 5) = (uint8_t) (x >> 16);
	*(str + 4) = (uint8_t) (x >> 24);
	*(str + 3) = (uint8_t) (x >> 32);
	*(str + 2) = (uint8_t) (x >> 40);
	*(str + 1) = (uint8_t) (x >> 48);
	*(str + 0) = (uint8_t) (x >> 56);
}

// Hash value representation (hexadecimal hash value represented by string)

string digestRepresentation(char* digest, unsigned size) {
	stringstream ss;
	ss << hex << setfill('0');
	for (unsigned i = 0; i < size; i++)
		ss << setw(2) << (unsigned) (uint8_t) digest[i];
	return ss.str();
}

// SHA-256 functions

void sha256_init(sha256_context* ctx) {
	for (unsigned i = 0; i < 8; i++)
		ctx->h[i] = sha256_h0[i];
	ctx->len = 0;
	ctx->totalLen = 0;
}

void sha256_transform(sha256_context* ctx, const unsigned char* msg, unsigned numBlocks) {
	uint32_t w[64];
	uint32_t v[8];
	for (unsigned i = 0; i < numBlocks; i++) {
		const unsigned char* block = msg + (i << 6);
		for (unsigned j = 0; j < 16; j++)
			pack32(&block[j << 2], w[j]);
		for (unsigned j = 16; j < 64; j++)
			w[j] = SHA256_S0(w[j - 2]) + w[j - 7] + SHA256_S1(w[j - 15]) + w[j - 16];
		for (unsigned j = 0; j < 8; j++)
			v[j] = ctx->h[j];
		for (unsigned j = 0; j < 64; j++) {
			uint32_t t1 = v[7] + SHA256_S2(v[4]) + CH(v[4], v[5], v[6]) + sha256_k[j] + w[j];
			uint32_t t2 = SHA256_S3(v[0]) + MAJ(v[0], v[1], v[2]);
			v[7] = v[6];
			v[6] = v[5];
			v[5] = v[4];
			v[4] = v[3] + t1;
			v[3] = v[2];
			v[2] = v[1];
			v[1] = v[0];
			v[0] = t1 + t2;
		}
		for (unsigned j = 0; j < 8; j++)
			ctx->h[j] += v[j];
	}
}

void sha256_update(sha256_context* ctx, const unsigned char* msg, unsigned len) {
	unsigned tmpLen = SHA256_BLOCK_SIZE - ctx->len;
	unsigned remLen = len < tmpLen ? len : tmpLen;
	memcpy(&ctx->block[ctx->len], msg, remLen);
	if (ctx->len + len < SHA256_BLOCK_SIZE) {
		ctx->len += len;
		return;
	}
	unsigned newLen = len - remLen;
	unsigned numBlocks = newLen / SHA256_BLOCK_SIZE;
	const unsigned char* remMsg = msg + remLen;
	sha256_transform(ctx, ctx->block, 1);
	sha256_transform(ctx, remMsg, numBlocks);
	remLen = newLen % SHA256_BLOCK_SIZE;
	memcpy(ctx->block, &remMsg[numBlocks << 6], remLen);
	ctx->len = remLen;
	ctx->totalLen += (numBlocks + 1) << 6;
}

void sha256_final(sha256_context* ctx, unsigned char* digest) {
	unsigned totalBits = (ctx->totalLen + ctx->len) << 3;
	unsigned numBlocks = (1 + ((SHA256_BLOCK_SIZE - 9) < (ctx->len % SHA256_BLOCK_SIZE)));
	unsigned lenBlocks = numBlocks << 6;
	memset(ctx->block + ctx->len, 0, lenBlocks - ctx->len);
	ctx->block[ctx->len] = 0x80;
	unpack32(totalBits, ctx->block + lenBlocks - 4);
	sha256_transform(ctx, ctx->block, numBlocks);
	for (unsigned i = 0; i < 8; i++)
		unpack32(ctx->h[i], &digest[i << 2]);
}

void sha256(const char* msg, unsigned len, char* digest) {
	sha256_context ctx;
	sha256_init(&ctx);
	sha256_update(&ctx, (const unsigned char*) msg, len);
	sha256_final(&ctx, (unsigned char*) digest);
}

void sha256(const string& msg, char* digest) {
	sha256(msg.c_str(), (unsigned) msg.length(), digest);
}

string sha256(const string& msg) {
	char digest[SHA256_DIGEST_SIZE];
	sha256(msg, digest);
	return digestRepresentation(digest, SHA256_DIGEST_SIZE);
}

// SHA-224 functions

void sha224_init(sha224_context* ctx) {
	for (unsigned i = 0; i < 8; i++)
		ctx->h[i] = sha224_h0[i];
	ctx->len = 0;
	ctx->totalLen = 0;
}

void sha224_update(sha224_context* ctx, const unsigned char* msg, unsigned len) {
	unsigned tmpLen = SHA224_BLOCK_SIZE - ctx->len;
	unsigned remLen = len < tmpLen ? len : tmpLen;
	memcpy(&ctx->block[ctx->len], msg, remLen);
	if (ctx->len + len < SHA224_BLOCK_SIZE) {
		ctx->len += len;
		return;
	}
	unsigned newLen = len - remLen;
	unsigned numBlocks = newLen / SHA224_BLOCK_SIZE;
	const unsigned char* remMsg = msg + remLen;
	sha256_transform(ctx, ctx->block, 1);
	sha256_transform(ctx, remMsg, numBlocks);
	remLen = newLen % SHA224_BLOCK_SIZE;
	memcpy(ctx->block, &remMsg[numBlocks << 6], remLen);
	ctx->len = remLen;
	ctx->totalLen += (numBlocks + 1) << 6;
}

void sha224_final(sha224_context* ctx, unsigned char* digest) {
	unsigned totalBits = (ctx->totalLen + ctx->len) << 3;
	unsigned numBlocks = (1 + ((SHA224_BLOCK_SIZE - 9) < (ctx->len % SHA224_BLOCK_SIZE)));
	unsigned lenBlocks = numBlocks << 6;
	memset(ctx->block + ctx->len, 0, lenBlocks - ctx->len);
	ctx->block[ctx->len] = 0x80;
	unpack32(totalBits, ctx->block + lenBlocks - 4);
	sha256_transform(ctx, ctx->block, numBlocks);
	for (unsigned i = 0; i < 7; i++)
		unpack32(ctx->h[i], &digest[i << 2]);
}

void sha224(const char* msg, unsigned len, char* digest) {
	sha224_context ctx;
	sha224_init(&ctx);
	sha224_update(&ctx, (const unsigned char*) msg, len);
	sha224_final(&ctx, (unsigned char*) digest);
}

void sha224(const string& msg, char* digest) {
	sha224(msg.c_str(), (unsigned) msg.length(), digest);
}

string sha224(const string& msg) {
	char digest[SHA224_DIGEST_SIZE];
	sha224(msg, digest);
	return digestRepresentation(digest, SHA224_DIGEST_SIZE);
}

// SHA-512 functions

void sha512_init(sha512_context* ctx) {
	for (unsigned i = 0; i < 8; i++)
		ctx->h[i] = sha512_h0[i];
	ctx->len = 0;
	ctx->totalLen = 0;
}

void sha512_transform(sha512_context* ctx, const unsigned char* msg, unsigned numBlocks) {
	uint64_t w[80];
	uint64_t v[8];
	for (unsigned i = 0; i < numBlocks; i++) {
		const unsigned char* block = msg + (i << 7);
		for (unsigned j = 0; j < 16; j++)
			pack64(&block[j << 3], w[j]);
		for (unsigned j = 16; j < 80; j++)
			w[j] = SHA512_S0(w[j - 2]) + w[j - 7] + SHA512_S1(w[j - 15]) + w[j - 16];
		for (unsigned j = 0; j < 8; j++)
			v[j] = ctx->h[j];
		for (unsigned j = 0; j < 80; j++) {
			uint64_t t1 = v[7] + SHA512_S2(v[4]) + CH(v[4], v[5], v[6]) + sha512_k[j] + w[j];
			uint64_t t2 = SHA512_S3(v[0]) + MAJ(v[0], v[1], v[2]);
			v[7] = v[6];
			v[6] = v[5];
			v[5] = v[4];
			v[4] = v[3] + t1;
			v[3] = v[2];
			v[2] = v[1];
			v[1] = v[0];
			v[0] = t1 + t2;
		}
		for (unsigned j = 0; j < 8; j++)
			ctx->h[j] += v[j];
	}
}

void sha512_update(sha512_context* ctx, const unsigned char* msg, unsigned len) {
	unsigned tmpLen = SHA512_BLOCK_SIZE - ctx->len;
	unsigned remLen = len < tmpLen ? len : tmpLen;
	memcpy(&ctx->block[ctx->len], msg, remLen);
	if (ctx->len + len < SHA512_BLOCK_SIZE) {
		ctx->len += len;
		return;
	}
	unsigned newLen = len - remLen;
	unsigned numBlocks = newLen / SHA512_BLOCK_SIZE;
	const unsigned char* remMsg = msg + remLen;
	sha512_transform(ctx, ctx->block, 1);
	sha512_transform(ctx, remMsg, numBlocks);
	remLen = newLen % SHA512_BLOCK_SIZE;
	memcpy(ctx->block, &remMsg[numBlocks << 7], remLen);
	ctx->len = remLen;
	ctx->totalLen += (numBlocks + 1) << 7;
}

void sha512_final(sha512_context* ctx, unsigned char* digest) {
	unsigned totalBits = (ctx->totalLen + ctx->len) << 3;
	unsigned numBlocks = 1 + ((SHA512_BLOCK_SIZE - 17) < (ctx->len % SHA512_BLOCK_SIZE));
	unsigned lenBlocks = numBlocks << 7;
	memset(ctx->block + ctx->len, 0, lenBlocks - ctx->len);
	ctx->block[ctx->len] = 0x80;
	unpack32(totalBits, ctx->block + lenBlocks - 4);
	sha512_transform(ctx, ctx->block, numBlocks);
	for (unsigned i = 0; i < 8; i++)
		unpack64(ctx->h[i], &digest[i << 3]);
}

void sha512(const char* msg, unsigned len, char* digest) {
	sha512_context ctx;
	sha512_init(&ctx);
	sha512_update(&ctx, (const unsigned char*) msg, len);
	sha512_final(&ctx, (unsigned char*) digest);
}

void sha512(const string& msg, char* digest) {
	sha512(msg.c_str(), (unsigned) msg.length(), digest);
}

string sha512(const string& msg) {
	char digest[SHA512_DIGEST_SIZE];
	sha512(msg, digest);
	return digestRepresentation(digest, SHA512_DIGEST_SIZE);
}

// SHA-384 functions

void sha384_init(sha384_context* ctx) {
	for (unsigned i = 0; i < 8; i++)
		ctx->h[i] = sha384_h0[i];
	ctx->len = 0;
	ctx->totalLen = 0;
}

void sha384_update(sha384_context* ctx, const unsigned char* msg, unsigned len) {
	unsigned tmpLen = SHA384_BLOCK_SIZE - ctx->len;
	unsigned remLen = len < tmpLen ? len : tmpLen;
	memcpy(&ctx->block[ctx->len], msg, remLen);
	if (ctx->len + len < SHA384_BLOCK_SIZE) {
		ctx->len += len;
		return;
	}
	unsigned newLen = len - remLen;
	unsigned numBlocks = newLen / SHA384_BLOCK_SIZE;
	const unsigned char* remMsg = msg + remLen;
	sha512_transform(ctx, ctx->block, 1);
	sha512_transform(ctx, remMsg, numBlocks);
	remLen = newLen % SHA384_BLOCK_SIZE;
	memcpy(ctx->block, &remMsg[numBlocks << 7], remLen);
	ctx->len = remLen;
	ctx->totalLen += (numBlocks + 1) << 7;
}

void sha384_final(sha384_context* ctx, unsigned char* digest) {
	unsigned totalBits = (ctx->totalLen + ctx->len) << 3;
	unsigned numBlocks = (1 + ((SHA384_BLOCK_SIZE - 17) < (ctx->len % SHA384_BLOCK_SIZE)));
	unsigned lenBlocks = numBlocks << 7;
	memset(ctx->block + ctx->len, 0, lenBlocks - ctx->len);
	ctx->block[ctx->len] = 0x80;
	unpack32(totalBits, ctx->block + lenBlocks - 4);
	sha512_transform(ctx, ctx->block, numBlocks);
	for (unsigned i = 0; i < 6; i++)
		unpack64(ctx->h[i], &digest[i << 3]);
}

void sha384(const char* msg, unsigned len, char* digest) {
	sha384_context ctx;
	sha384_init(&ctx);
	sha384_update(&ctx, (const unsigned char*) msg, len);
	sha384_final(&ctx, (unsigned char*) digest);
}

void sha384(const string& msg, char* digest) {
	sha384(msg.c_str(), (unsigned) msg.length(), digest);
}

string sha384(const string& msg) {
	char digest[SHA384_DIGEST_SIZE];
	sha384(msg, digest);
	return digestRepresentation(digest, SHA384_DIGEST_SIZE);
}

// SHA-512/224 functions

void sha512_224_init(sha512_context* ctx) {
	for (unsigned i = 0; i < 8; i++)
		ctx->h[i] = sha512_224_h0[i];
	ctx->len = 0;
	ctx->totalLen = 0;
}

void sha512_224(const char* msg, unsigned len, char* digest) {
	sha512_context ctx;
	sha512_224_init(&ctx);
	sha512_update(&ctx, (const unsigned char*) msg, len);
	sha512_final(&ctx, (unsigned char*) digest);
}

void sha512_224(const string& msg, char* digest) {
	sha512_224(msg.c_str(), (unsigned) msg.length(), digest);
}

string sha512_224(const string& msg) {
	char digest[SHA512_DIGEST_SIZE];
	sha512_224(msg, digest);
	return digestRepresentation(digest, SHA224_DIGEST_SIZE);
}

// SHA-512/256 functions

void sha512_256_init(sha512_context* ctx) {
	for (unsigned i = 0; i < 8; i++)
		ctx->h[i] = sha512_256_h0[i];
	ctx->len = 0;
	ctx->totalLen = 0;
}

void sha512_256(const char* msg, unsigned len, char* digest) {
	sha512_context ctx;
	sha512_256_init(&ctx);
	sha512_update(&ctx, (const unsigned char*) msg, len);
	sha512_final(&ctx, (unsigned char*) digest);
}

void sha512_256(const string& msg, char* digest) {
	sha512_256(msg.c_str(), (unsigned) msg.length(), digest);
}

string sha512_256(const string& msg) {
	char digest[SHA512_DIGEST_SIZE];
	sha512_256(msg, digest);
	return digestRepresentation(digest, SHA256_DIGEST_SIZE);
}

}
}
