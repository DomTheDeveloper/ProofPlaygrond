// C++17. Classify binary matrices by their powers, then lift square-zero matrices.
#include <array>
#include <cstdint>
#include <iostream>

using Bits = std::uint32_t;
using Count = std::uint64_t;

template <int D>
Count lifts_mod_four(const std::array<unsigned, D>& rows) {
    // X + 2Y squares to zero modulo 4 iff XY + YX = -X^2/2 modulo 2.
    // The right side uses ordinary integer matrix multiplication on 0/1 entries.
    constexpr int variables = D * D;
    constexpr Bits rhs_column = Bits{1} << variables;
    std::array<Bits, variables> pivots{};
    int rank = 0;
    for (int i = 0; i < D; ++i) {
        for (int j = 0; j < D; ++j) {
            Bits equation = 0;
            unsigned square_entry = 0;
            for (int k = 0; k < D; ++k) {
                unsigned xik = (rows[i] >> k) & 1U;
                unsigned xkj = (rows[k] >> j) & 1U;
                square_entry += xik * xkj;
                if (xik) equation ^= Bits{1} << (k * D + j);
                if (xkj) equation ^= Bits{1} << (i * D + k);
            }
            if (square_entry & 1U) return 0;
            if ((square_entry / 2) & 1U) equation |= rhs_column;
            while (equation & (rhs_column - 1)) {
                int column = __builtin_ctz(equation);
                if (pivots[column] == 0) {
                    pivots[column] = equation;
                    ++rank;
                    break;
                }
                equation ^= pivots[column];
            }
            if (equation == rhs_column) return 0;
        }
    }
    return Count{1} << (variables - rank);
}

template <int D>
void enumerate() {
    constexpr unsigned row_values = 1U << D;
    constexpr Bits total = Bits{1} << (D * D);
    std::array<Count, D + 1> indices{};
    Count lifts = 0;
    for (Bits packed = 0; packed < total; ++packed) {
        std::array<unsigned, D> rows{};
        std::array<unsigned, row_values> times_matrix{};
        for (int i = 0; i < D; ++i) {
            rows[i] = (packed >> (i * D)) & (row_values - 1);
            // Row v times this matrix is the XOR of the rows selected by v.
            for (unsigned v = 0; v < (1U << i); ++v) {
                times_matrix[v + (1U << i)] = times_matrix[v] ^ rows[i];
            }
        }
        auto power = rows;
        for (int exponent = 1; exponent <= D; ++exponent) {
            unsigned any = 0;
            for (unsigned row : power) any |= row;
            if (any == 0) {
                ++indices[exponent];
                if (exponent <= 2) lifts += lifts_mod_four<D>(rows);
                break;
            }
            for (auto& row : power) row = times_matrix[row];
        }
    }
    // CSV: dimension, matrices inspected, square-zero lifts to Z/4, counts by index.
    std::cout << D << ',' << total << ',' << lifts;
    for (int k = 1; k <= D; ++k) std::cout << ',' << indices[k];
    std::cout << '\n';
}

int main() {
    enumerate<1>();
    enumerate<2>();
    enumerate<3>();
    enumerate<4>();
    enumerate<5>();
}
