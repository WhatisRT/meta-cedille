{ nixpkgs ? import <nixpkgs> {} }:
let fetchFromGitHub = nixpkgs.fetchFromGitHub;
    nixpkgsArgs = (if nixpkgs.system == "aarch64-darwin" then { system = "x86_64-darwin"; } else { });
    pinnedPkgs = import (fetchFromGitHub {
      owner = "NixOS";
      repo = "nixpkgs";
      rev = "aec48af439d69dbde35e3141d5980bc8804d518d";
      sha256 = "NDAflAkWdSLQcER8/S0FAQUr9m5pbdqKtif2N79/h/c=";
    }) nixpkgsArgs;
    ghcpkgs = nixpkgs; # in case we need a different GHC

    profiledHaskellPackages = (import <nixpkgs> nixpkgsArgs).haskellPackages.override {
      overrides = hself: hsuper: rec {
        mkDerivation = args: hsuper.mkDerivation (args // {
          enableLibraryProfiling = true;
        });
      };
    };

    meta-cedille-src = with pinnedPkgs.agdaPackages; mkDerivation {
      pname = "meta-cedille-src";
      version = "0.9";
      src = ./.;
      meta = {};
      buildInputs = [ standard-library ];
      everythingFile = "src/meta-cedille.agda";
      buildPhase = "cd src; agda -c --ghc-dont-call-ghc --compile-dir $out meta-cedille.agda; cd ..";
      installPhase = "cp -r src stdlib-exts test bootstrap $out";
      extraExtensions = [ "hs" "mced" ];
    };

    meta-cedille-gen = with pinnedPkgs; localGhcpkgs: stdenv.mkDerivation {
      name = "meta-cedille";
      src = "${meta-cedille-src}";
      buildInputs = [
        (agda.withPackages {
          pkgs = [ agdaPackages.standard-library ];
          ghc = localGhcpkgs.ghcWithPackages (pkgs: with pkgs; [ ieee bytestring-trie containers ]);
        })
      ];
      buildPhase = ''
        cd src
        agda --ghc --ghc-flag=-O2 --ghc-flag=-j$NIX_BUILD_CORES meta-cedille.agda
        cd ..'';
      installPhase = ''
        mkdir $out && mkdir $out/bin && mkdir $out/share
        cp src/meta-cedille $out/bin
        cp -r bootstrap $out/share
      '';
    };

    self = with pinnedPkgs; {
      meta-cedille-src = meta-cedille-src;

      meta-cedille = meta-cedille-gen ghcpkgs.haskellPackages;

      # meta-cedille-prof = (meta-cedille-gen profiledHaskellPackages).overrideAttrs (old: {
      #   buildInputs = old.buildInputs ++ [ nixpkgs.haskellPackages.profiteur ];
      #   name = "meta-cedille-prof";
      #   buildPhase = ''
      #     cd src
      #     agda --ghc --ghc-flag=-j4 --ghc-flag=-prof --ghc-flag=-fprof-auto meta-cedille.agda
      #     cd ..'';
      #   installPhase = ''
      #     mkdir $out && cp src/meta-cedille $out/
      #     $out/meta-cedille +RTS -p -po$out/meta-cedille-1 -RTS --no-repl &
      #     $out/meta-cedille +RTS -p -po$out/meta-cedille-2 -RTS --no-repl --load test/Test &
      #     wait
      #     cd $out
      #     profiteur meta-cedille-1.prof
      #     profiteur meta-cedille-2.prof'';
      # });

      tests = stdenv.mkDerivation {
        name = "meta-cedille-tests";
        src = "${self.meta-cedille}";
        buildInputs = [ time ];
        buildPhase = ''
          ${time}/bin/time -o test-time-1 ./bin/meta-cedille --no-repl &
          ${time}/bin/time -o test-time-2 ./bin/meta-cedille --no-repl --load test/Test &
          wait'';
        installPhase = "mkdir $out && cp test-time-* $out";
      };

      benchmarks = stdenv.mkDerivation {
        name = "meta-cedille-benchmarks";
        src = ./.;
        buildInputs = [ bench self.meta-cedille ];
        buildPhase = ''
                   bench '${self.meta-cedille}/bin/meta-cedille --no-repl' '${self.meta-cedille}/bin/meta-cedille --load test/Test --no-repl' --output bench.html
                   '';
        installPhase = "mkdir $out && cp bench.html $out";
      };
    };
in self
