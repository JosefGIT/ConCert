From ConCert.Examples.Ecommerce Require Import Ecommerce.
From ConCert.Utils Require Import Automation.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ChainedList.
From ConCert.Execution Require Import Containers.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Examples.Ecommerce Require Import EcommerceGens.
From ConCert.Examples.Ecommerce Require Import EcommercePrinters.
Require Import Extras.
From Coq Require Import List.
From Coq Require Import ZArith.
Import ListNotations.
Section EcommerceTestSetup.

  Definition ecommerce_contract_addr := contract_base_addr.
  Definition seller := creator.
  
  Definition setup :=
      {|
        setup_listings := FMap.empty;
        setup_timeout := 3
      |}.

  Definition deploy_ecommerce := create_deployment 0 Ecommerce.contract setup.

  Definition ecommerce_chainbuilder :=
    unpack_result (TraceGens.add_block empty_chain
    [
      build_act creator creator (Blockchain.act_transfer person_1 30);
      build_act creator creator (Blockchain.act_transfer person_2 15);
      build_act creator creator (deploy_ecommerce)
    ]).

End EcommerceTestSetup.

Module TestInfo <: EcommerceGensInfo.
  Definition contract_addr := ecommerce_contract_addr.
  Definition buyers := [person_1; person_2].
  Definition item_ids := [1%nat; 2%nat].
End TestInfo.
Module MG := EcommerceGens.EcommerceGens TestInfo.
Import MG.

Module NotationInfo <: TestNotationParameters.
  Definition gAction := gEcommerceAction.
  Definition init_cb := ecommerce_chainbuilder.
End NotationInfo.
Module TN := TestNotations NotationInfo.
Import TN.

(* Sample to check quality of generated chains. *)
(* Sample gChain. *)

Definition sum_act_transfer (acts : list ActionBody) :=
  sumZ (fun act => match act with 
                    | act_transfer _ amount => amount
                    | _ => 0
                    end) acts.
(*
Definition purchase_exists (state : Ecommerce.State) (msg : Ecommerce.Msg) : bool :=
  match FMap.find purchaseId state.(purchases) with
  | Some _ => true
  | _ => false
  end.

Definition msg_is_request_purchase (state : Ecommerce.State) (msg : Ecommerce.Msg) :=
  match msg with
  | buyer_request_purchase _ _  => true
  | _=> false
  end.

Definition msg_is_buyer_abort (state : Ecommerce.State) (msg : Ecommerce.Msg) :=
  match msg with
  | buyer_abort _  => true
  | _=> false
  end.
  

Definition amount_sent_is_item_value_of_purchase
  (chain : Chain) (cctx : ContractCallContext) (old_state : Ecommerce.State)
  (msg : Msg) (result_opt : option (Ecommerce.State * list ActionBody)) :=
  match result_opt with
  | Some (_, acts) =>
      match FMap.find purchaseId old_state.(purchases) with
      | Some purchase =>
          match FMap.find purchase.(item) old_state.(listings) with
          | Some _item =>
                checker(sum_act_transfer acts =? _item.(item_value))
          | _ => checker false (* should never occur *)
          end
      | _ => checker false
      end
  | _ => checker false (* should never occur *)
  end.

(* on [buyer_abort], amount transferred to buyer is equal to item_value in the purchase. *)
(* FAILS! *)
(*
QuickChick(
  {{ fun state msg => purchase_exists state msg && msg_is_buyer_abort state msg }}
  contract_base_addr
  {{ amount_sent_is_item_value_of_purchase }}
).
*)
*)
Definition no_precondition (state : Ecommerce.State) (msg : Ecommerce.Msg) := true.

Definition purchase_is_finished purchase :=
  match purchase.(purchase_state) with
  | Ecommerce.completed | Ecommerce.rejected | Ecommerce.failed => true
  | _ => false
  end.

  



Definition listings_cannot_be_changed_while_active_purchase
  (chain : Chain) (cctx : ContractCallContext) (old_state : Ecommerce.State)
  (msg : Msg) (result_opt : option (Ecommerce.State * list ActionBody)) :=
  match result_opt with
  | Some (_,_) =>
    match msg with
    |  seller_update_listings itemId _ _ =>
      let purchases_with_itemId := filter (fun purchase => (purchase.(item) =? itemId)%nat) (FMap.values old_state.(purchases)) in
      checker (forallb (fun purchase => purchase_is_finished purchase) purchases_with_itemId)
    | _ => checker true
    end
  | None => checker true
  end.
(* Listing cannot be changed while being purchased. *)
QuickChick({{ no_precondition }} contract_base_addr {{ listings_cannot_be_changed_while_active_purchase }}).