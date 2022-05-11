{ nixpkgs ? <nixpkgs> }:
let fetchFromGitHub = (import <nixpkgs> {}).fetchFromGitHub;
    pinnedPkgs = import (fetchFromGitHub {
      owner = "NixOS";
      repo = "nixpkgs";
      rev = "08dc90729fc8b4ab072607cf7257900a9cacb1f6";
      sha256 = "oieO93uofWhvmbsV62mBBW+75/KZq42Osmn0mLTnA5E=";
    }) {};
    ghcpkgs = pinnedPkgs; # in case we need a different GHC
in with pinnedPkgs;
stdenv.mkDerivation {
  name = "meta-cedille";
  src = ./.;
  buildInputs = [
    (agda.withPackages {
      pkgs = [ agdaPackages.standard-library ];
      ghc = ghcpkgs.haskellPackages.ghcWithPackages (pkgs: with pkgs; [ ieee bytestring-trie ]);
    })
  ];
  buildPhase = ''
             cd src
             agda --ghc meta-cedille.agda
             '';
  installPhase = "mkdir $out && cp meta-cedille $out/";
}
