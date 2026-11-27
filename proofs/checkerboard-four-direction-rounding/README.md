# Integral rounding in four checkerboard directions

The July 15 manuscript applies Kahn’s hypergraph edge-coloring theorem after constructing a diffuse fractional packing. It obtains the same leading coefficient for integral and fractional packings for each checkerboard class. The directions are rows, columns and diagonals of slopes +1 and −1. The exact continuum calculation and its earlier formalization are documented in the [continuum audit](https://github.com/DomTheDeveloper/crl/pull/141) and [four-direction project](https://github.com/DomTheDeveloper/crl/pull/34).

The CSV records finite integral values for side lengths 5 through 24. The Python verifier uses NumPy, SciPy and HiGHS. It checks incidences and finite integer programs. The asymptotic argument is in the manuscript, submitted here for review. AI assistance was used.
