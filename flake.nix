{
  description = "ezsys: system helpers for Bend 2";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  # bendlang/bend's flake at the commit that packages 2.0.38 (the v2.0.38 tag
  # may still package 2.0.37)
  inputs.bend = {
    url = "github:bendlang/bend/042e797ebd1cfc060603e2682879909fe86fa8c2";
    inputs.nixpkgs.follows = "nixpkgs";
  };
  # Interim: ez 1.5.0 does not build on 2.0.38 yet, so ez and bolt stay on
  # the bend ez's own flake.lock records (2.0.36). The package, its proofs
  # and the entry check build on this flake's bend (2.0.38). A tooling pass
  # puts `inputs.bend.follows = "bend"` and ez.mkProofs back once ez
  # releases on 2.0.38.
  inputs.ez = {
    url = "github:Emerging-Patterns/ez";
    inputs.nixpkgs.follows = "nixpkgs";
    inputs.bend.url = "github:bendlang/bend/eebc18cd04daeade06c3f68c3c96c1faefd3462f";
  };

  outputs = { self, nixpkgs, ... }@inputs:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      version = "0.0.0"; # x-release-please-version
      ez = inputs.ez.lib.${system};
      ezBin = inputs.ez.packages.${system}.default;
      bend = inputs.bend.packages.${system}.default;
      bolt = ez.toolPackage { name = "bolt"; src = self; wrapFlags = [ "--gpu" "off" ]; };
      bend-cc = ez.bend-cc;
      llvm = pkgs.llvmPackages_19;
    in {
      packages.${system} = {
        inherit bend bend-cc;
        ez = ezBin;
        inherit bolt;
      };

      checks.${system} = {
        # every PROOF.bend checks on this flake's bend (interim stand-in for
        # ez.mkProofs, whose `ez prove` runs on ez's bend)
        proofs = pkgs.runCommand "ezsys-proofs" {
          nativeBuildInputs = [ bend ];
          BEND_LIB = ez.bendLib ./ez.lock.toml;
        } ''
          export HOME=$TMPDIR
          cp -r ${self} src && chmod -R u+w src && cd src
          for p in $(find . -name PROOF.bend -not -path './.ez/*' | sort); do
            first=$(cd "$(dirname "$p")" && bend "$(basename "$p")" | head -n 1)
            echo "$p: $first"
            [ "$first" = "ALL PROOFS CHECK" ] || exit 1
          done
          touch $out
        '';
        # ENTRY.bend states the laws on main.bend, which reaches src/sys.bend's
        # foreign effects, so its verdict is SOME PROOFS FAIL; its only error
        # may be the list of defs relying on unsafe or foreign code (2.0.38
        # prints it as `defs that depend on ...:` lines and a Hint).
        entry = pkgs.runCommand "ezsys-entry" {
          nativeBuildInputs = [ bend ];
          BEND_LIB = ez.bendLib ./ez.lock.toml;
        } ''
          export HOME=$TMPDIR
          cp -r ${self} src && chmod -R u+w src && cd src
          out_entry=$(bend ENTRY.bend 2>&1 || true)
          echo "$out_entry" | head -n 2
          [ "$(echo "$out_entry" | sed -n 1p)" = "SOME PROOFS FAIL" ] || exit 1
          echo "$out_entry" | sed -n 2p \
            | grep -Eq '^Error: [0-9]+ defs? rel(y|ies) on unsafe or foreign code:$' || exit 1
          if echo "$out_entry" | tail -n +3 \
            | grep -Ev '^defs that depend on (@unsafe|foreign effects): |^Hint: ' \
            | grep -q .; then
            echo "$out_entry"; exit 1
          fi
          touch $out
        '';
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

      devShells.${system}.default = ez.mkShell {
        src = self;
        packages = [
          bend
          bend-cc
          ezBin
        ];
      };
    };
}
