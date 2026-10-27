{
  description = "ezsys: system helpers for Bend 2";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  # bendlang/bend's flake at the commit that packages 2.0.38 (the v2.0.38 tag
  # may still package 2.0.37)
  inputs.bend = {
    url = "github:bendlang/bend/042e797ebd1cfc060603e2682879909fe86fa8c2";
    inputs.nixpkgs.follows = "nixpkgs";
  };
  inputs.ez = {
    url = "github:Emerging-Patterns/ez";
    inputs.nixpkgs.follows = "nixpkgs";
    inputs.bend.follows = "bend";
  };

  outputs = { self, nixpkgs, ... }@inputs:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" ];
      forEach = nixpkgs.lib.genAttrs systems;
      outputsFor = system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
          version = "0.1.0"; # x-release-please-version
          ez = inputs.ez.lib.${system};
          ezBin = inputs.ez.packages.${system}.default;
          bend = inputs.bend.packages.${system}.default;
          bolt = ez.toolPackage { name = "bolt"; src = self; inherit bend; wrapFlags = ez.rtsFlags bend [ "--gpu" "off" ]; };
          bend-cc = ez.bend-cc;
          llvm = pkgs.llvmPackages_19;
        in {
          packages = {
            inherit bend bend-cc;
            ez = ezBin;
            inherit bolt;
          };

          checks = {
            proofs = ez.mkProofs { ez = ezBin; src = self; };
            # examples/smoke on the C lane: build it, save a file atomically, read
            # it back, read a missing file, print the wall clock, which must
            # be within a few seconds of `date -u`, list the directory and a
            # missing one. A smoke run, not evidence for
            # any SPEC.md row.
            smoke = pkgs.runCommand "ezsys-smoke" {
              nativeBuildInputs = [ bend llvm.clang ];
              BEND_LIB = ez.bendLib ./ez.lock.toml;
              BEND_NO_TELEMETRY = "1";
            } ''
              export HOME=$TMPDIR CC=${llvm.clang}/bin/clang
              cp -r ${self} src && chmod -R u+w src && cd src/examples/smoke
              bend main.bend -o smoke
              mkdir -p $TMPDIR/smoke
              touch "$TMPDIR/smoke/b b" "$TMPDIR/smoke/.hidden" "$TMPDIR/smoke/héllo"
              before=$(date -u +%s)
              got=$(SMOKE_DIR=$TMPDIR/smoke ./smoke)
              after=$(date -u +%s)
              echo "$got"
              echo "$got" | grep -qx 'saved' || exit 1
              echo "$got" | grep -qx 'read back: héllo, ezsys' || exit 1
              echo "$got" | grep -qx 'FAIL 2 No such file or directory' || exit 1
              [ ! -e $TMPDIR/smoke/ezsys-smoke.txt.tmp ] || exit 1
              echo "$got" | grep -qx 'env: fallback' || exit 1
              now=$(echo "$got" | sed -n 's/^now: //p')
              echo "$now" | grep -Eqx '[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}\.[0-9]{3}Z' || exit 1
              at=$(date -u -d "$(echo "$now" | sed 's/T/ /; s/Z$//')" +%s)
              [ "$at" -ge "$((before - 2))" ] && [ "$at" -le "$((after + 2))" ] || exit 1
              [ "$(echo "$got" | sed -n 's/^week: //p')" = "$(date -u +%G-W%V)" ] || exit 1
              echo "$got" | grep -qF "Hello Noah, it is $now {{unknown}}" || exit 1
              echo "$got" | grep -qx '  <li>pylon</li>' || exit 1
              echo "$got" | grep -qx 'text: STRASSE|a,b,c|ΑΒ  |' || exit 1
              # dir.list: names sorted by code point, no . or .., then a missing
              # directory written as Python's OSError
              echo "$got" | sed -n '/^list:$/,$p' | sed -n '2,5p' > listed
              printf '%s\n' .hidden 'b b' ezsys-smoke.txt 'héllo' | diff - listed || exit 1
              echo "$got" | grep -qxF "[Errno 2] No such file or directory: '$TMPDIR/smoke/no-such-dir'" || exit 1
              touch $out
            '';
            lint = ez.mkLint { src = self; };
          };

          devShells.default = ez.mkShell {
            src = self;
            packages = [
              bend
              bend-cc
              ezBin
            ];
          };
        };
      perSystem = forEach outputsFor;
      each = name: forEach (system: perSystem.${system}.${name});
    in {
      packages = each "packages";
      checks = each "checks";
      devShells = each "devShells";
    };
}
