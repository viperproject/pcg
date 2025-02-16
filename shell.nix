{
  pkgs ? import <nixpkgs> {}
}:

let
  toolchainTOML = builtins.fromTOML(builtins.readFile ./rust-toolchain);
  channel = toolchainTOML.toolchain.channel;
  components = toolchainTOML.toolchain.components;
  # Strip the "nightly-" prefix from the channel name
  rustNightly = pkgs.rust-bin.nightly.${builtins.substring 8 10 channel}.default.override {
    extensions = components;
  };
in
pkgs.mkShell {
  buildInputs = with pkgs; [
    openssl
    pkg-config
    rustNightly
    libiconv
    zlib
  ] ++ (if pkgs.stdenv.isDarwin then [
    darwin.apple_sdk.frameworks.Security
    darwin.apple_sdk.frameworks.SystemConfiguration
  ] else []);

  shellHook = ''
    export OPENSSL_DIR="${pkgs.openssl.dev}"
    export OPENSSL_LIB_DIR="${pkgs.openssl.out}/lib"
    export OPENSSL_INCLUDE_DIR="${pkgs.openssl.dev}/include"
  '';
}
