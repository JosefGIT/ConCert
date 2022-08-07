From ConCert.Examples.Ecommerce Require Import Ecommerce.
From ConCert.Utils Require Import Automation.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ChainedList.
From ConCert.Execution Require Import Containers.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Examples.Ecommerce Require Import EcommerceGens.
From ConCert.Examples.Ecommerce Require Import EcommercePrinters.
From Coq Require Import List.
From Coq Require Import ZArith.
Import ListNotations.
Section EcommerceTestSetup.

  Definition ecommerce_contract_addr := contract_base_addr.
  Definition seller := creator.
  
  Definition item_1 := {|
    item_value := 6;
    item_description := "Item1"
  |}.
  Definition item_2 := {|
    item_value := 3;
    item_description := "Item2"
  |}.

  
  Definition setup :=
      {|
        setup_listings := FMap.add 2 item_2 (FMap.add 1 item_1 FMap.empty);
        setup_timeout := 5
      |}.

  Definition deploy_ecommerce := create_deployment 0 Ecommerce.contract setup.

  Definition ecommerce_chainbuilder :=
    unpack_result (TraceGens.add_block empty_chain
    [
      build_act creator creator (Blockchain.act_transfer person_1 1);
      build_act creator creator (deploy_ecommerce)
    ]).
    
    
End EcommerceTestSetup.

Module TestInfo <: EcommerceGensInfo.
  Definition contract_addr := ecommerce_contract_addr.
  Definition purchase_buyer := person_1.
End TestInfo.
Module MG := EcommerceGens.EcommerceGens TestInfo.
Import MG.

Module NotationInfo <: TestNotationParameters.
  Definition gAction := gEcommerceAction.
  Definition init_cb := ecommerce_chainbuilder.
End NotationInfo.
Module TN := TestNotations NotationInfo.
Import TN.

Check gChain.
(* Sample to check quality of generated chains. *)
Sample gChain.