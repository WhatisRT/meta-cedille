{ nixpkgs ? <nixpkgs> }:
let fetchFromGitHub = (import <nixpkgs> {}).fetchFromGitHub;
    pinnedPkgs = import (fetchFromGitHub {
      owner = "NixOS";
      repo = "nixpkgs";
      rev = "08dc90729fc8b4ab072607cf7257900a9cacb1f6";
      sha256 = "oieO93uofWhvmbsV62mBBW+75/KZq42Osmn0mLTnA5E=";
    }) {};
    ghcpkgs = pinnedPkgs; # in case we need a different GHC

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
                  agda --ghc meta-cedille.agda
                  '';
      installPhase = "mkdir $out && cp meta-cedille $out/";
    };

    self = with pinnedPkgs;
  {
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
