{
  description = "Node ";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";

  };
  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
    }:
    with flake-utils.lib;
    eachSystem allSystems (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in
      rec {

        devShell = pkgs.mkShell {
          name = "
          slides-dev-shell
          ";
          buildInputs = with pkgs; [ nodejs_24 pnpm ]; 
        };

      }
    );
}
