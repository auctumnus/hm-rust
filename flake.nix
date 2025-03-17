{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs = {
        nixpkgs.follows = "nixpkgs";
      };
    };
  };
  outputs = { self, nixpkgs, flake-utils, rust-overlay }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          overlays = [ (import rust-overlay) ];
          pkgs = import nixpkgs {
            inherit system overlays;
          };
          rustToolchain = pkgs.rust-bin.nightly."2025-03-01".default.override {
            extensions = [ "rust-src" "llvm-tools-preview" ];
          };
        in
        with pkgs;
        {
          devShells.default = mkShell {
            buildInputs = [
              rustToolchain
              cargo-llvm-cov
              just
            ];
          };
        }
      );
}
