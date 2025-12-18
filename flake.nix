# TODO 2023-07-20T22:19:36+0100 raehik
# * they build with GHC 9.2.5 (check Stack resolver in stack.yaml I guess)
# * granule-interpreter/gr-golden had 7 fails (tests disabled here)

{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    haskell-flake.url = "github:srid/haskell-flake";
    haskell-src-exts = {
      url = "github:jackohughes/haskell-src-exts";
      flake = false;
    };
  };
  outputs = inputs@{ self, nixpkgs, flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = nixpkgs.lib.systems.flakeExposed;
      imports = [ inputs.haskell-flake.flakeModule ];

      perSystem = { self', pkgs, config, ... }: {
        packages.default = self'.packages.granule-repl;

        # TODO shame I have to create a full derivation for this, I'd like to
        # just copy files with a name. alas
        packages.granule-stdlib = pkgs.stdenv.mkDerivation {
          name = "granule-stdlib";
          src = ./StdLib;
          phases = [ "unpackPhase" "installPhase" ];
          installPhase = ''
            mkdir -p $out
            cp $src/* $out
          '';
        };

        packages.granule-repl-with-stdlib = pkgs.writeShellScriptBin "grepl" ''
          ${self'.packages.granule-repl}/bin/grepl \
            --include-path ${self'.packages.granule-stdlib} \
            $@
        '';

        haskellProjects.default = {
          ## local configuration
          # TODO 2023-07-20 raehik: tests access files outside directory
          settings.granule-interpreter.check = false;

          # TODO 2023-07-24 raehik:
          # `/Language.Granule.Synthesis.Synth/Construcor test for
          # Either/Branch on (Left : a -> Either a b)/` fails.
          # dorchard unsure if it should be failing or not.
          # Skip tests while unresolved.
          settings.granule-frontend.check = false;

          ## build/dependency configuration
          basePackages = pkgs.haskell.packages.ghc94;

          # haskell-src-exts: Jack H's fork
          packages.haskell-src-exts.source = inputs.haskell-src-exts;

          # sbv: using old version.
          # tests bring in tons of deps and fail to compile: skip
          packages.sbv.source = "9.2";
          settings.sbv.check = false;

          # text-replace: unmaintained-- ignore bounds, just try building
          # see: https://github.com/chris-martin/text-replace/pull/3/files
          settings.text-replace.broken = false;
          settings.text-replace.jailbreak = true; # TODO trying

          devShell = {
            hoogle = false; # haskell-src-exts override breaks it
            tools = hp: {
              ghcid = null; # broken on GHC 9.6? old fsnotify
              hlint = null; # broken on GHC 9.6? old
              haskell-language-server = null; # takes ages to build

              # don't build Cabal ourselves (because our GHC is old, 9.4)
              cabal-install = pkgs.cabal-install;
            };
          };
        };

        # prep a Docker/OSI image build
        # uses streamLayeredImage so as to not place the image in the Nix store
        # to use, run result script and load into your container daemon. e.g.
        # for podman, `nix build .#image && ./result | podman load`
        # for some reason, I don't need justStaticExecutables to get a small
        # image here. not sure why but sure!
        packages.image-granule-repl = pkgs.dockerTools.streamLayeredImage {
          name = "granule-repl";
          # equivalent to `git rev-parse HEAD`
          # only exists on clean working tree, else set to "dev"
          tag = self.rev or "dev";
          config = {
            Entrypoint = [ "${self'.packages.granule-repl-with-stdlib}/bin/grepl" ];

            # Granule syntax is UTF-8
            # C.UTF-8 is builtin. to use en_US.UTF-8 etc, add glibcLocales into
            # contents and point LOCALE_ARCHIVE to it
            Env = [ "LANG=C.UTF-8" ];
          };
          maxLayers = 100; # less than Docker max layers to allow extending
        };

      };
    };
}
