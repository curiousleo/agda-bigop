{
  pkgs ? import ./nix/nixpkgs.nix { },
}:
with pkgs;
mkShell {
  buildInputs = [
    agda
  ];
}
