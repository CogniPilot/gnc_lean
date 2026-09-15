{ pkgs }:
let
  arch = {
    x86_64-linux = {
      target = "x86_64-unknown-linux-musl";
      sha256 = "46564c5a15b0a5919dee06b246ac1297399968c828269f675212104d7d1ac445";
    };
    aarch64-linux = {
      target = "aarch64-unknown-linux-musl";
      sha256 = "92a8585cb841eaecae3aaf3e8d84bf4cd0b2cdbae09e2e9e605418f6e38b2133";
    };
  }.${pkgs.stdenv.hostPlatform.system};
in {
  leantar = pkgs.stdenv.mkDerivation {
    pname = "leantar";
    version = "0.1.17";
    src = pkgs.fetchurl {
      url = "https://github.com/digama0/leangz/releases/download/v0.1.17/leantar-v0.1.17-${arch.target}.tar.gz";
      inherit (arch) sha256;
    };
    dontBuild = true;
    installPhase = ''
      mkdir -p "$out/bin"
      cp leantar "$out/bin/"
    '';
  };
  proofwidgets = pkgs.runCommand "proofwidgets-assets-0.0.95-lean-4.29.1" {
    src = pkgs.fetchurl {
      url = "https://github.com/leanprover-community/ProofWidgets4/releases/download/v0.0.95%2Blean-v4.29.1/ProofWidgets4.tar.gz";
      sha256 = "566d7e9b0b81b62bb45d72cfd787f4c372a82a3326db23a6bea284ee89b473cb";
    };
  } ''
    mkdir -p "$out"
    tar -xzf "$src" -C "$out"
  '';
}
