{ nixpkgs ?  <nixpkgs> }:
let ghcpkgs = import ((import <nixpkgs> {}).fetchFromGitHub {
      owner = "NixOS";
      repo = "nixpkgs";
      rev = "068984c00e0d4e54b6684d98f6ac47c92dcb642e";
      sha256 = "00j4xv4lhhqwry7jd67brnws4pwb8vn660n43pvxpkalbpxszwfg";
    }) {}; # pinned to 20.09, as bytestring-trie is broken later
    oldpkgs = import ((import <nixpkgs> {}).fetchFromGitHub {
      owner = "NixOS";
      repo = "nixpkgs";
      rev = "a165aeceda9f9741d15bc2488425daeb06c0707e";
      sha256 = "0bshzligqwbjlvx4jygv6k4c54mjdvj1d7xmfzgjl6hhybh3wjpd";
    }) {}; # pinned to 21.05
in with oldpkgs;
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
