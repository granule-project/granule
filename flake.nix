# TODO 2023-07-20T22:19:36+0100 raehik
# * they build with GHC 9.2.5 (check Stack resolver in stack.yaml I guess)
# * granule-interpreter/gr-golden had 7 fails (tests disabled here)

{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    haskell-flake.url = "github:srid/haskell-flake";
  };
  outputs = inputs@{ self, nixpkgs, flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = nixpkgs.lib.systems.flakeExposed;
      imports = [ inputs.haskell-flake.flakeModule ];

      perSystem = { self', pkgs, config, ... }: {
        packages.default = self'.packages.granule-repl;
        #haskellProjects.ghc96 = import ./haskell-flake-ghc96.nix pkgs;
        haskellProjects.default = {
          #basePackages = config.haskellProjects.ghc96.outputs.finalPackages;
          settings = {
            sbv = {
              # 2023-04-18 raehik: sbv-9.0 broken; seems tests fail. ignore
              check = false;
              broken = false;
            };

            granule-interpreter = {
              # TODO 2023-07-20 raehik: accesses files outside directory
              check = false;
            };
          };

          devShell = {
            tools = hp: {
              ghcid = null; # broken on GHC 9.6? old fsnotify
              hlint = null; # broken on GHC 9.6? old
              haskell-language-server = null; # TAKES AGES TO BUILD FFS
            };
          };
        };

        # `nix build .#image` preps a Docker/OSI image build
        # uses streamLayeredImage so as to not place the image in the Nix store
        # to use, run result script and load into your container daemon. e.g.
        # for podman, `nix build .#image && ./result | podman load`
        # for some reason, I don't need justStaticExecutables to get a small
        # image here. not sure why but sure!
        packages.image = pkgs.dockerTools.streamLayeredImage {
          name = "granule-repl";
          # equivalent to `git rev-parse HEAD`
          # only exists on clean working tree, else set to "dev"
          tag = self.rev or "dev";
          config = {
            Entrypoint = [ "${pkgs.lib.getExe self'.packages.granule-repl}" ];
          };
          #contents = [ self'.packages.granule-repl ];
          maxLayers = 100; # less than Docker max layers to allow extending
        };

      };
    };
}
