{ pkgs ? import <nixpkgs> {} }:
(pkgs.buildFHSUserEnv {
  name = "coq-esy-shell";
  targetPkgs = pkgs: (with pkgs; [
    autoconf
    automake
    coq
    gcc
    gnum4
    gnumake
    gnupatch
    nodePackages.esy
    which
  ]);
  runScript = "esy zsh";
}).env
