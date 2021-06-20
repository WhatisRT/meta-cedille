{ nixpkgs ?  <nixpkgs> }:
let oldpkgs = (import ((import <nixpkgs> {}).fetchFromGitHub {
      owner = "NixOS";
      repo = "nixpkgs";
      rev = "497587ae2f47ff0b364aedde2c1172068ebc58d8";
      sha256 = "11f3b08qqy5v7y39s76658da2kq37gpahhn8ghav3xg6q04dvyl3";
    }) {}); # pinned to 20.09, as bytestring-trie is broken later
in with (import <nixpkgs> {});
stdenv.mkDerivation {
  name = "meta-cedille";
  src = ./.;
  buildInputs = [
    (agda.withPackages {
      pkgs = [ agdaPackages.standard-library ];
      ghc = oldpkgs.haskellPackages.ghcWithPackages (pkgs: with pkgs; [ ieee bytestring-trie ]);
    })
  ];
  buildPhase = ''
             cd src
             agda --ghc meta-cedille.agda
             '';
  installPhase = "mkdir $out && cp meta-cedille $out/";
}
