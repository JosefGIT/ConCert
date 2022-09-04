From ConCert.Examples.Ecommerce Require Import EcommerceFixed.
From ConCert.Utils Require Import Automation.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ChainedList.
From ConCert.Execution Require Import Containers.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Examples.Ecommerce Require Import EcommerceFixedGens.
From ConCert.Examples.Ecommerce Require Import EcommerceFixedPrinters.
Require Import Extras.
From Coq Require Import List.
From Coq Require Import ZArith.
Import ListNotations.
Section EcommerceFixedTestSetup.

  Definition ecommerce_contract_addr := contract_base_addr.
  Definition seller := creator.
  
  (* In these tests we only consider a contract instance with one item and one purchase. *)
  Definition item_1 := {|
    item_value := 1;
    item_description := "Item1"
  |}.
  
  Definition item1_Id := 42%nat.
  Definition setup :=
      {|
        setup_listings := FMap.add item1_Id item_1 FMap.empty;(* FMap.add 2 item_2 (FMap.add 1 item_1 FMap.empty); *)
        setup_timeout := 3
      |}.

  Definition deploy_ecommerce := create_deployment 0 EcommerceFixed.contract setup.

  Definition ecommerce_chainbuilder :=
    unpack_result (TraceGens.add_block empty_chain
    [
      build_act creator creator (Blockchain.act_transfer person_1 30);
      build_act creator creator (deploy_ecommerce)
    ]).

  (* In EcommerceGens the request_purchase is set to be called happen in the second block, hence "2".
     This purchaseId is used throughout these tests.
  *)
  Definition purchaseId := hash_purchaseId 2%nat person_1.
End EcommerceFixedTestSetup.

Module TestInfo <: EcommerceFixedGensInfo.
  Definition contract_addr := ecommerce_contract_addr.
  Definition purchase_buyer := person_1.
  Definition item1_Id := item1_Id.
  Definition purchaseId := purchaseId.
End TestInfo.
Module MG := EcommerceFixedGens.EcommerceFixedGens TestInfo.
Import MG.

Module NotationInfo <: TestNotationParameters.
  Definition gAction := gEcommerceFixedAction.
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

(* This one is probably not necessary since the purchase will always exist in these tests *)
Definition purchase_exists (state : EcommerceFixed.State) (msg : EcommerceFixed.Msg) : bool :=
  match FMap.find purchaseId state.(purchases) with
  | Some _ => true
  | _ => false
  end.

Definition msg_is_request_purchase (state : EcommerceFixed.State) (msg : EcommerceFixed.Msg) :=
  match msg with
  | buyer_request_purchase _ _  => true
  | _=> false
  end.

Definition msg_is_buyer_abort (state : EcommerceFixed.State) (msg : EcommerceFixed.Msg) :=
  match msg with
  | buyer_abort _  => true
  | _=> false
  end.
  

Definition amount_sent_is_item_value_of_purchase
  (chain : Chain) (cctx : ContractCallContext) (old_state : EcommerceFixed.State)
  (msg : Msg) (result_opt : option (EcommerceFixed.State * list ActionBody)) :=
  match result_opt with
  | Some (_, acts) =>
      match FMap.find purchaseId old_state.(purchases) with
      | Some purchase =>
          match FMap.find purchase.(itemId) old_state.(listings) with
          | Some _item =>
                checker(sum_act_transfer acts =? _item.(item_value))
          | _ => checker false (* should never occur *)
          end
      | _ => checker false
      end
  | _ => checker false (* should never occur *)
  end.

(* on [buyer_abort], amount transferred to buyer is equal to item_value in the purchase. *)
(* QuickChick(
  {{ fun state msg => purchase_exists state msg && msg_is_buyer_abort state msg }}
  contract_base_addr
  {{ amount_sent_is_item_value_of_purchase }}
). *)
(* +++ Passed 10000 tests (0 discards) *)

Definition is_purchase_state (purchase_state_goal : EcommerceFixed.PurchaseState) (chain_state : ChainState) :=
  match get_contract_state EcommerceFixed.State chain_state ecommerce_contract_addr with
  | Some state =>
      match FMap.find purchaseId state.(purchases) with
          | Some purchase => purchase_state_eq purchase.(purchase_state) purchase_state_goal
          | _ => false
      end
  | None => false (* should never occur *)
  end.
(* on purchase initialization (that is purchase with state [request_purchase])
   all states are reachable for the purchae*)
(*QuickChick (ecommerce_chainbuilder ~~> is_purchase_state EcommerceFixed.requested).
QuickChick (ecommerce_chainbuilder ~~> is_purchase_state EcommerceFixed.accepted).
QuickChick (ecommerce_chainbuilder ~~> is_purchase_state EcommerceFixed.rejected).
QuickChick (ecommerce_chainbuilder ~~> is_purchase_state EcommerceFixed.delivered).
QuickChick (ecommerce_chainbuilder ~~> is_purchase_state EcommerceFixed.completed).
QuickChick (ecommerce_chainbuilder ~~> is_purchase_state EcommerceFixed.dispute).
QuickChick (ecommerce_chainbuilder ~~> is_purchase_state EcommerceFixed.counter).
QuickChick (ecommerce_chainbuilder ~~> is_purchase_state EcommerceFixed.failed).*)
(* Success - found witness satisfying the predicate! *)


(* TODO? *)
(* If all purchases are of state [failed] [completed] or [rejected] then the contract should
   contain no money. *)