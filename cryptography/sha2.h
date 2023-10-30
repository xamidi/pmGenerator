#ifndef XAMIDI_CRYPTOGRAPHY_SHA2_H
#define XAMIDI_CRYPTOGRAPHY_SHA2_H

#include <cstdint>
#include <string>

namespace xamidi {
namespace cryptography {

void sha2_sample();

std::string sha224(const std::string& msg);
void sha224(const std::string& msg, char* digest);
void sha224(const char* msg, unsigned len, char* digest);

std::string sha256(const std::string& msg);
void sha256(const std::string& msg, char* digest);
void sha256(const char* msg, unsigned len, char* digest);

std::string sha384(const std::string& msg);
void sha384(const std::string& msg, char* digest);
void sha384(const char* msg, unsigned len, char* digest);

std::string sha512(const std::string& msg);
void sha512(const std::string& msg, char* digest);
void sha512(const char* msg, unsigned len, char* digest);

std::string sha512_224(const std::string& msg);
void sha512_224(const std::string& msg, char* digest);
void sha512_224(const char* msg, unsigned len, char* digest);

std::string sha512_256(const std::string& msg);
void sha512_256(const std::string& msg, char* digest);
void sha512_256(const char* msg, unsigned len, char* digest);

#define SHA224_DIGEST_SIZE (224 / 8)
#define SHA256_DIGEST_SIZE (256 / 8)
#define SHA384_DIGEST_SIZE (384 / 8)
#define SHA512_DIGEST_SIZE (512 / 8)

#define SHA256_BLOCK_SIZE ( 512 / 8)
#define SHA512_BLOCK_SIZE (1024 / 8)
#define SHA384_BLOCK_SIZE SHA512_BLOCK_SIZE
#define SHA224_BLOCK_SIZE SHA256_BLOCK_SIZE

typedef struct {
	unsigned len;
	unsigned totalLen;
	std::uint32_t h[8];
	unsigned char block[2 * SHA256_BLOCK_SIZE];
} sha256_context;
typedef struct {
	unsigned len;
	unsigned totalLen;
	std::uint64_t h[8];
	unsigned char block[2 * SHA512_BLOCK_SIZE];
} sha512_context;
typedef sha512_context sha384_context;
typedef sha256_context sha224_context;

}
}

#endif // XAMIDI_CRYPTOGRAPHY_SHA2_H
