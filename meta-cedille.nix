# This is a very hacky solution, I'll update this once
# https://github.com/NixOS/nixpkgs/pull/76653 is merged

let
  unstable = import ((import <nixpkgs> {}).fetchFromGitHub {
    owner = "NixOS";
    repo = "nixpkgs";
    rev = "fcf547d0e23b4be19fdd877a1e31dff0d0b0498d";
    sha256 = "1jl6lrlgxcc8mj65gqvjj6i25vkm8cjbqr8d5fn1m9aki08sdrww";
  }) {};
  AgdaStdlib-1_3 = unstable.AgdaStdlib.overrideAttrs (oldAttrs:
    {
      version = "1.3";
      name = "agda-stdlib-1.3";
      src = unstable.fetchFromGitHub {
        repo = "agda-stdlib";
        owner = "agda";
        rev = "v1.3";
        sha256 = "18kl20z3bjfgx5m3nvrdj5776qmpi7jl2p12pqybsls2lf86m0d5";
      };
      postInstall = ''
                  rm -rf $out/share/agda/*
                  cp -pR _build src *.agda-lib $out/share/agda
                  '';
      topSourceDirectories = [ "." ];
    });
  ghc = unstable.haskellPackages.ghcWithPackages (pkgs: with pkgs; [ ieee bytestring-trie ]);
in
unstable.agda.mkDerivation(self: {
  name = "meta-cedille";
  src = ./.;
  everythingFile = "meta-cedille.agda";
  buildDepends = [ AgdaStdlib-1_3 ghc ];
  buildPhase = ''
             echo ${AgdaStdlib-1_3.out}/share/agda/standard-library.agda-lib > libraries
             cd src
             agda --ghc --library-file=../libraries meta-cedille.agda
             '';
  installPhase = "mkdir $out && cp meta-cedille $out/";
})
