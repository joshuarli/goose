// Goose compiler — SHA-256 and the digest type the stable keys are made of.
// Implemented here because the keys need nothing else from a hashing
// library, and a dependency would buy no more than these hundred lines.
#pragma once

namespace goose {

// A SHA-256 digest. Keys store the first 128 bits (Stored); names built from
// them use the first 64 (Short).
struct Digest {
    uint8_t b[32] = {};

    bool operator==(const Digest &o) const { return memcmp(b, o.b, sizeof b) == 0; }
    bool operator!=(const Digest &o) const { return !(*this == o); }
    bool operator<(const Digest &o) const { return memcmp(b, o.b, sizeof b) < 0; }

    string Hex(size_t bytes = 32) const {
        static const char *digits = "0123456789abcdef";
        string s;
        for (size_t i = 0; i < bytes && i < sizeof b; i++) {
            s += digits[b[i] >> 4];
            s += digits[b[i] & 15];
        }
        return s;
    }
    string Short() const { return Hex(8); }
    string Stored() const { return Hex(16); }
};

struct DigestHash {
    size_t operator()(const Digest &d) const {
        size_t h;
        memcpy(&h, d.b, sizeof h);
        return h;
    }
};

class Sha256 {
    uint32_t h[8] = { 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
                      0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 };
    uint8_t block[64];
    size_t used = 0;
    uint64_t total = 0;

    static uint32_t Rotr(uint32_t x, int n) { return (x >> n) | (x << (32 - n)); }

    void Compress(const uint8_t *p) {
        static const uint32_t k[64] = {
            0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
            0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
            0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
            0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
            0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
            0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
            0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
            0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
            0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
            0xc67178f2 };
        uint32_t w[64];
        for (int i = 0; i < 16; i++)
            w[i] = (uint32_t)p[4 * i] << 24 | (uint32_t)p[4 * i + 1] << 16 |
                   (uint32_t)p[4 * i + 2] << 8 | (uint32_t)p[4 * i + 3];
        for (int i = 16; i < 64; i++) {
            auto s0 = Rotr(w[i - 15], 7) ^ Rotr(w[i - 15], 18) ^ (w[i - 15] >> 3);
            auto s1 = Rotr(w[i - 2], 17) ^ Rotr(w[i - 2], 19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16] + s0 + w[i - 7] + s1;
        }
        auto a = h[0], b = h[1], c = h[2], d = h[3], e = h[4], f = h[5], g = h[6], hh = h[7];
        for (int i = 0; i < 64; i++) {
            auto t1 = hh + (Rotr(e, 6) ^ Rotr(e, 11) ^ Rotr(e, 25)) + ((e & f) ^ (~e & g)) +
                      k[i] + w[i];
            auto t2 = (Rotr(a, 2) ^ Rotr(a, 13) ^ Rotr(a, 22)) + ((a & b) ^ (a & c) ^ (b & c));
            hh = g; g = f; f = e; e = d + t1; d = c; c = b; b = a; a = t1 + t2;
        }
        h[0] += a; h[1] += b; h[2] += c; h[3] += d;
        h[4] += e; h[5] += f; h[6] += g; h[7] += hh;
    }

public:
    void Update(const void *data, size_t n) {
        auto p = (const uint8_t *)data;
        total += n;
        while (n) {
            auto take = min(n, sizeof block - used);
            memcpy(block + used, p, take);
            used += take;
            p += take;
            n -= take;
            if (used == sizeof block) {
                Compress(block);
                used = 0;
            }
        }
    }
    void Update(string_view s) { Update(s.data(), s.size()); }

    Digest Final() {
        auto bits = total * 8;
        uint8_t pad[72] = { 0x80 };
        // Pad to 56 mod 64, then the 64-bit big-endian bit length.
        auto zeros = used < 56 ? 56 - used : 120 - used;
        Update(pad, zeros);
        uint8_t len[8];
        for (int i = 0; i < 8; i++) len[i] = (uint8_t)(bits >> (56 - 8 * i));
        Update(len, 8);
        Digest d;
        for (int i = 0; i < 8; i++)
            for (int j = 0; j < 4; j++) d.b[4 * i + j] = (uint8_t)(h[i] >> (24 - 8 * j));
        return d;
    }

    static Digest Of(string_view s) {
        Sha256 sha;
        sha.Update(s);
        return sha.Final();
    }
};

}  // namespace goose
