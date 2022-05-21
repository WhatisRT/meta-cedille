{ nixpkgs ? import <nixpkgs> {} }:
let fetchFromGitHub = nixpkgs.fetchFromGitHub;
    pinnedPkgs = import (fetchFromGitHub {
      owner = "NixOS";
      repo = "nixpkgs";
      rev = "aec48af439d69dbde35e3141d5980bc8804d518d";
      sha256 = "NDAflAkWdSLQcER8/S0FAQUr9m5pbdqKtif2N79/h/c=";
    }) {};
    ghcpkgs = nixpkgs; # in case we need a different GHC

    meta-cedille-gen = with pinnedPkgs; ghcpkgs: stdenv.mkDerivation {
      name = "meta-cedille";
      src = ./.;
      buildInputs = [
        (agda.withPackages {
          pkgs = [ agdaPackages.standard-library ];
          ghc = ghcpkgs.ghcWithPackages (pkgs: with pkgs; [ ieee bytestring-trie ]);
        })
      ];
      buildPhase = ''
                  cd src
                  agda --ghc --ghc-flag=-O2 meta-cedille.agda
                  '';
      installPhase = "mkdir $out && cp meta-cedille $out/";
    };

    self = with pinnedPkgs; {
      meta-cedille = meta-cedille-gen ghcpkgs.haskellPackages;

      tests = stdenv.mkDerivation {
        name = "meta-cedille-tests";
        src = ./.;
        buildInputs = [ time self.meta-cedille ];
        buildPhase = ''
          ${time}/bin/time -o test-time-1 ${self.meta-cedille}/meta-cedille --no-repl &
          ${time}/bin/time -o test-time-2 ${self.meta-cedille}/meta-cedille --load test/Test --no-repl &
          wait
                     '';
        installPhase = "mkdir $out && cp test-time-* $out";
      };
    };
in self
