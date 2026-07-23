// Replay a CHCEXP01 compact Chomp response certificate without using the P-position oracle.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using Position = std::array<uint8_t, 10>;
struct Record { uint32_t next; uint8_t row; uint8_t target; uint16_t reserved; };
static_assert(sizeof(Record) == 8);

static uint64_t pack(const Position& p) {
    uint64_t z = 0;
    for (int i = 0; i < 10; ++i) z |= static_cast<uint64_t>(p[i]) << (6 * i);
    return z;
}
static Position unpack(uint64_t z) {
    Position p{};
    for (int i = 0; i < 10; ++i) p[i] = static_cast<uint8_t>((z >> (6 * i)) & 63U);
    return p;
}
static int area(const Position& p) { int s = 0; for (uint8_t x : p) s += x; return s; }
static Position bite(const Position& p, int row, int target) {
    Position q = p;
    for (int j = row; j < 10; ++j) q[j] = static_cast<uint8_t>(std::min<int>(q[j], target));
    return q;
}
static bool ferrers(const Position& p) {
    if (p[0] == 0 || p[0] > 42) return false;
    for (int i = 1; i < 10; ++i) if (p[i] > p[i-1]) return false;
    return true;
}

int main(int argc, char** argv) {
    try {
        if (argc != 2) { std::cerr << "usage: " << argv[0] << " CERT.bin\n"; return 2; }
        std::ifstream in(argv[1], std::ios::binary);
        if (!in) throw std::runtime_error("cannot open certificate");
        char magic[8]; uint64_t n = 0, expected_records = 0;
        in.read(magic, 8); in.read(reinterpret_cast<char*>(&n), 8);
        in.read(reinterpret_cast<char*>(&expected_records), 8);
        if (!in || std::string(magic, 8) != "CHCEXP01" || n == 0 || n > UINT32_MAX)
            throw std::runtime_error("bad certificate header");
        std::vector<uint64_t> keys(n);
        in.read(reinterpret_cast<char*>(keys.data()), static_cast<std::streamsize>(n * 8));
        if (!in || !std::is_sorted(keys.begin(), keys.end()) ||
            std::adjacent_find(keys.begin(), keys.end()) != keys.end())
            throw std::runtime_error("carrier keys not strictly sorted");
        std::vector<Position> positions; positions.reserve(n);
        for (uint64_t key : keys) {
            Position p = unpack(key);
            if (pack(p) != key || !ferrers(p)) throw std::runtime_error("invalid carrier position");
            positions.push_back(p);
        }
        const std::array<Position, 3> roots = {{
            {{42,42,42,42,35,35,35,35,35,35}},
            {{42,42,42,42,42,42,29,29,29,29}},
            {{42,42,42,42,42,42,42,25,25,25}}
        }};
        for (const Position& root : roots)
            if (!std::binary_search(keys.begin(), keys.end(), pack(root)))
                throw std::runtime_error("target root missing");

        uint64_t records = 0;
        for (uint64_t i = 0; i < n; ++i) {
            const Position& p = positions[i];
            uint32_t count = 0; in.read(reinterpret_cast<char*>(&count), 4);
            if (!in || count != static_cast<uint32_t>(area(p) - 1))
                throw std::runtime_error("wrong response count");
            for (int first_row = 0; first_row < 10; ++first_row) {
                const int low = first_row == 0 ? 1 : 0;
                for (int first_target = low; first_target < p[first_row]; ++first_target) {
                    Record rec{}; in.read(reinterpret_cast<char*>(&rec), sizeof(rec));
                    if (!in || rec.reserved != 0 || rec.next >= n)
                        throw std::runtime_error("invalid response record");
                    const Position q = bite(p, first_row, first_target);
                    if (rec.row >= 10 || rec.target >= q[rec.row] ||
                        (rec.row == 0 && rec.target == 0))
                        throw std::runtime_error("illegal response template");
                    if (bite(q, rec.row, rec.target) != positions[rec.next])
                        throw std::runtime_error("response target mismatch");
                    ++records;
                }
            }
        }
        char extra;
        if (records != expected_records || in.read(&extra, 1))
            throw std::runtime_error("certificate length mismatch");
        std::cout << "VERIFIED carrier=" << n << " records=" << records << '\n';
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "error: " << e.what() << '\n';
        return 1;
    }
}
