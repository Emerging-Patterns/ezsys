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
