## Liquid Queues

This is a Thesis project for exploring Liquid Haskell, a program verifier for
the programming language Haskell which allows specifying correctness properties by using refinement types.

As an application, we verify different implementations of priority queues.

This project consist of code in `[code](code/)` and the Thesis pdf in [thesis](thesis/thesis.pdf)


## Table of Content
- [Installation](#installation)
- [References](#references)
- [License](#license)

## Installation
For reliable setup, both for compiling latex and running liquidhaskell project,
is recommended to use `nix` with `flake`. However,
you are free to install the depencies in your preferred way.

1. Install Nix [installation guide](https://nixos.org/download/#nix-install-linux)
2. Enable flake option ([Flakes](https://nixos.wiki/wiki/Flakes))
3. In either `code` or `thesis` direcotry run `nix develop`

## References
- [LiquidHaskell Doc](https://ucsd-progsys.github.io/liquidhaskell/)
- [LiquidHaskell Lectures](https://nikivazou.github.io/lh-course/Lecture_01_RefinementTypes.html)

## License
MIT License
see [LICENSE](LICENSE) file for details
