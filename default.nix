with (import <nixpkgs> {}); 
myEnvFun {
  name = "shake-env";
  buildInputs = [
    (with haskellPackages; ghcWithPackagesOld (self: [
       Agda 
       AgdaStdlib
       optparseApplicative
       regexApplicative
       shake
       tasty
       tastyHunit
     ]))
  ];
}
