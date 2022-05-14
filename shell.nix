with import <nixpkgs> {};
(callPackage ./default.nix {}).meta-cedille.overrideAttrs (old: {src = null;})
