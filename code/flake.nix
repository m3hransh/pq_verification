{
  description = "LiquidHaskell Project";

  inputs.nixpkgs.url = "nixpkgs/nixos-25.05";

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux"; # or use builtins.currentSystem if available
      pkgs = nixpkgs.legacyPackages.${system};

      compilerVersion = "ghc9101";
    in
    {
      devShell.${system} = pkgs.mkShell {
        buildInputs = with pkgs; [
          z3
          stack
          haskell.packages."${"ghc948"}".ghcid
          haskell.packages."${compilerVersion}".haskell-language-server
          cabal-install
          haskell.packages.${compilerVersion}.ghc
        ];
      };
    };
}
