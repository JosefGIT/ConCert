
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.Test Require Import QCTest.
Import MonadNotation.
From Coq Require Import ZArith.
From Coq Require Import List.

Module Type EcommerceGensInfo.
  Parameter contract_addr : Address.
End EcommerceGensInfo.


Module EcommerceGens (Info : EcommerceGensInfo).
Import Info.

Definition Env := Environment.
Open Scope Z_scope.

Definition gEcommerceMsg (env : Env): GOpt Action := returnGen None.

End EcommerceGens.