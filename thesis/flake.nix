{
  description = "LaTeX Document Demo";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.05";
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
        tex = pkgs.texlive.combine {
          inherit (pkgs.texlive)
            scheme-medium
            titling
            csquotes
            todonotes
            latexmk
            pgf
            biber
            koma-script
            biblatex
            blindtext
            nicematrix
            fontspec
            ;
        };
      in
      rec {

        devShell = pkgs.mkShell {
          name = "
          latex-demo-shell
          ";
          buildInputs = [ tex ];
        };

        packages = {

          document = pkgs.stdenvNoCC.mkDerivation rec {
            name = "
          latex-demo-document
          ";
            src = self;
            buildInputs = [
              pkgs.coreutils
              tex
            ];
            phases = [
              "
          unpackPhase
          "
              "
          buildPhase
          "
              "
          installPhase
          "
            ];
            buildPhase = ''
              export PATH="${pkgs.lib.makeBinPath buildInputs}";
              mkdir -p .cache/texmf-var
              env TEXMFHOME=.cache TEXMFVAR=.cache/texmf-var \
                SOURCE_DATE_EPOCH=${toString self.lastModified} \
                latexmk -interaction=nonstopmode -pdf -lualatex \
                -pretex="\pdfvariable
              suppressoptionalinfo
              512\relax
              " \
                    -usepretex main.tex
            '';
            installPhase = ''
              mkdir -p $out
              cp main.pdf $out/
            '';
          };
        };
        defaultPackage = packages.document;
      }
    );
}
