# qpt-parity
Implementation of iterative algorithm to decide parity games, using succinct winning statistics.
It is available in both C++17 and Haskell.
To compile Haskell version, install container-0.5.10.2 via cabal and compile `ordered.hs` with `ghc`
To compile C++17 version, make sure GCC version is 7+ and build target `fast` for optimised solver; or build target `fastrmcycle` for solver with winning cycle elimination.
