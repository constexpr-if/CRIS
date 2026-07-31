{
  description = "CRIS development environment";
  inputs = {
    nixpkgs.url = "github:snu-sf/nixpkgs/rocq-env-0.2";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      nixpkgs,
      flake-utils,
      ...
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
        };
        coq = pkgs.coq_9_0;
        coqPackages = pkgs.mkCoqPackages coq;
        callPackage = pkgs.lib.callPackageWith (pkgs // params // set);
        params = {
          inherit (coqPackages) mkCoqDerivation lib stdlib;
          inherit (coq) ocamlPackages;
        };
        set = {
          inherit coq;
          paco = callPackage coqPackages.paco.override { version = "4.2.3"; };
          ExtLib = callPackage coqPackages.ExtLib.override { version = "0.13.0"; };
          ITree = callPackage coqPackages.ITree.override { version = "5.2.1"; };
          Ordinal = callPackage coqPackages.Ordinal.override { version = "0.5.6"; };
          stdpp = callPackage coqPackages.stdpp.override { version = "1.12.0"; };
          iris = callPackage coqPackages.iris.override { version = "4.4.0"; };
        };
      in
      rec {
        devShell = pkgs.mkShell {
          buildInputs = pkgs.lib.attrValues set ++ [
            coqPackages.vsrocq-language-server
            pkgs.coqtail-mcp
          ];
        };
        packages.default = packages.CRIS;
        packages.CRIS = coqPackages.mkCoqDerivation {
          owner = "constexpr-if";
          pname = "CRIS";
          defaultVersion = "v2026-07-22";
          release = {
            v2026-07-22 = {
              rev = "b3559dad899f8f397101b17693b75878668778e0";
              sha256 = "sha256-3rhNRsYXofYtVu0tVNzlU7qo0uyVb7kZPT7wTPQa7mI=";
            };
            workshop = {
              rev = "c0bcd04e7ddfed32f1d7b8e5e2e328e3b5957bdd";
              sha256 = "sha256-6REga0gV0F4rTL3sU785Tn68kzSl+bnVDgSse3NHeKw=";
            };
          };
          propagatedBuildInputs = pkgs.lib.attrValues set;
          dontConfigure = true;
          installPhase = ''
            runHook preInstall
            make -f Makefile.coq install \
              COQLIBINSTALL=$out/lib/coq/${coqPackages.coq}/user-contrib
            runHook postInstall
          '';
        };

      }
    );
}
