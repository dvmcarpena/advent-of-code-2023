{
  description = "Agda + Standard Library";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = nixpkgs.legacyPackages."${system}";
        in
        {
          devShells.default = pkgs.mkShell {
            name = "Agda + Standard Library";

            # Build tools
            packages = with pkgs; [
              (agda.withPackages (ps: [
                ps.standard-library
              ]))
            ];
          };

          devShell = self.devShells."${system}".default;
        });
}
