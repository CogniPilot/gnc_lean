{
  description = "GNC: verified geometry for guidance, navigation and control";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/fd1462031fdee08f65fd0b4c6b64e22239a77870";
    mathlib = { url = "github:leanprover-community/mathlib4/5e932f97dd25535344f80f9dd8da3aab83df0fe6"; flake = false; };
    batteries = { url = "github:leanprover-community/batteries/756e3321fd3b02a85ffda19fef789916223e578c"; flake = false; };
    Qq = { url = "github:leanprover-community/quote4/707efb56d0696634e9e965523a1bbe9ac6ce141d"; flake = false; };
    aesop = { url = "github:leanprover-community/aesop/7152850e7b216a0d409701617721b6e469d34bf6"; flake = false; };
    proofwidgets = { url = "github:leanprover-community/ProofWidgets4/4dd0959c44d1af0462bd604d0f87c5781307d709"; flake = false; };
    importGraph = { url = "github:leanprover-community/import-graph/48d5698bc464786347c1b0d859b18f938420f060"; flake = false; };
    LeanSearchClient = { url = "github:leanprover-community/LeanSearchClient/c5d5b8fe6e5158def25cd28eb94e4141ad97c843"; flake = false; };
    plausible = { url = "github:leanprover-community/plausible/83e90935a17ca19ebe4b7893c7f7066e266f50d3"; flake = false; };
    Cli = { url = "github:leanprover/lean4-cli/7802da01beb530bf051ab657443f9cd9bc3e1a29"; flake = false; };
  };
  outputs = inputs@{ nixpkgs, ... }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" ];
      eachSystem = f: nixpkgs.lib.genAttrs systems (system: f (import nixpkgs { inherit system; }));
      dependencyNames = [ "mathlib" "batteries" "Qq" "aesop" "proofwidgets"
        "importGraph" "LeanSearchClient" "plausible" "Cli" ];
      dependencies = nixpkgs.lib.genAttrs dependencyNames (name: {
        path = toString inputs.${name};
        rev = inputs.${name}.rev;
      });
    in {
      packages = eachSystem (pkgs: {
        lean = import ./nix/lean.nix { inherit pkgs; };
        default = inputs.self.packages.${pkgs.stdenv.hostPlatform.system}.lean;
      });
      devShells = eachSystem (pkgs: let
        lean = import ./nix/lean.nix { inherit pkgs; };
        cacheTools = import ./nix/cache-tools.nix { inherit pkgs; };
        dependencySpec = pkgs.writeText "gnc-dependencies.json" (builtins.toJSON dependencies);
        setup = pkgs.writeShellScriptBin "gnc-setup" ''
          exec ${pkgs.python3}/bin/python3 ${./scripts/setup.py} ${dependencySpec} ${cacheTools.proofwidgets} "$@"
        '';
        cache = pkgs.writeShellScriptBin "gnc-cache" ''
          set -euo pipefail
          ${setup}/bin/gnc-setup
          export MATHLIB_CACHE_DIR="$(realpath -m "''${MATHLIB_CACHE_DIR:-$PWD/.lake/mathlib-cache}")"
          mkdir -p "$MATHLIB_CACHE_DIR"
          # Upstream 0.1.17 detection does not trim the version's newline.
          # Its versioned binary path bypasses that check and uses our hash pin.
          if [ ! -e "$MATHLIB_CACHE_DIR/leantar-0.1.17" ]; then
            ln -s ${cacheTools.leantar}/bin/leantar "$MATHLIB_CACHE_DIR/leantar-0.1.17"
          fi
          lake build cache
          # Run the unmodified upstream cache tool from mathlib's root. This
          # avoids treating our Nix path manifest as a conflicting Git pin.
          lake env bash -c '
            cd .lake/packages/mathlib
            exec .lake/build/bin/cache get --repo=leanprover-community/mathlib4 --skip-proofwidgets "$@"
          ' gnc-cache "$@"
        '';
      in {
        default = pkgs.mkShell {
          GNC_LEAN_BIN = "${lean}/bin/lean";
          GNC_DEPENDENCY_SPEC = toString dependencySpec;
          # Bound concurrent Lake compiler processes for large rational
          # certificates. Override inside the shell for a different host.
          LEAN_NUM_THREADS = "2";
          packages = [ lean setup cache cacheTools.leantar pkgs.gcc pkgs.git pkgs.curl pkgs.ripgrep
            pkgs.python3 pkgs.poppler-utils pkgs.zstd ];
          shellHook = ''
            if [ -f lakefile.toml ]; then
              gnc-setup
            fi
          '';
        };
      });
    };
}
