{ pkgs }:
let
  archives = {
    x86_64-linux = {
      platform = "linux";
      sha256 = "bf062d29556d655685fb287563c249ad6a8fde34352c18b5e32568a595c1aec1";
    };
    aarch64-linux = {
      platform = "linux_aarch64";
      sha256 = "1ccdfb7f924901f4b73a4b4eb169e5b3dc74f6836521b47e733ea25f2abfc0dc";
    };
  };
  archive = archives.${pkgs.stdenv.hostPlatform.system};
in pkgs.stdenv.mkDerivation {
  pname = "lean-official";
  version = "4.29.1";
  src = pkgs.fetchurl {
    url = "https://github.com/leanprover/lean4/releases/download/v4.29.1/lean-4.29.1-${archive.platform}.tar.zst";
    inherit (archive) sha256;
  };
  nativeBuildInputs = [ pkgs.zstd pkgs.autoPatchelfHook pkgs.makeWrapper ];
  buildInputs = [ pkgs.stdenv.cc.cc.lib pkgs.gmp pkgs.libuv pkgs.zlib ];
  dontBuild = true;
  installPhase = ''
    runHook preInstall
    mkdir -p "$out"
    cp -a . "$out/"
    runHook postInstall
  '';
  postFixup = ''
    wrapProgram "$out/bin/lake" --set LEAN_CC ${pkgs.gcc}/bin/cc
    wrapProgram "$out/bin/leanc" --set LEAN_CC ${pkgs.gcc}/bin/cc
  '';
}
