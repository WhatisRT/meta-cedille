with import <nixpkgs> {};
(callPackage ./default.nix {}).overrideAttrs (old: {src = null;})
