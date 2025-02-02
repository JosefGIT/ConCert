From ConCert.Examples.Ecommerce Require Import EcommerceFixed.
From ConCert.Utils Require Import Automation.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ChainedList.
From ConCert.Execution Require Import Containers.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Examples.Ecommerce Require Import EcommerceFixedGens.
From ConCert.Examples.Ecommerce Require Import EcommerceFixedPrinters.
From ConCert.Execution Require Import Serializable.
Require Import Extras.
From Coq Require Import List.
From Coq Require Import ZArith.
Import ListNotations.
Section EcommerceFixedTestSetup.

  Definition ecommerce_contract_addr := contract_base_addr.
  Definition seller := creator.
  
  Definition setup :=
      {|
        setup_listings := FMap.empty;
        setup_timeout := 3
      |}.

  Definition deploy_ecommerce := create_deployment 0 EcommerceFixed.contract setup.

  Definition ecommerce_chainbuilder :=
    unpack_result (TraceGens.add_block empty_chain
    [
      build_act creator creator (Blockchain.act_transfer person_1 30);
      build_act creator creator (Blockchain.act_transfer person_2 15);
      build_act creator creator (deploy_ecommerce)
    ]).

End EcommerceFixedTestSetup.

Module TestInfo <: EcommerceFixedGensInfo.
  Definition contract_addr := ecommerce_contract_addr.
  Definition buyers := [person_1; person_2].
  Definition item_ids := [1%nat; 2%nat].
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

(*Definition purchase_state_is (purchase_state' : EcommerceFixed.PurchaseState) (state : EcommerceFixed.State) : bool :=
  match FMap.find purchaseId state.(purchases) with
  | Some purchase => purchase_state_eq purchase.(purchase_state) purchase_state'
  | _ => false
  end.*)

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
  
Definition msg_is_seller_call_timeout (state : EcommerceFixed.State) (msg : EcommerceFixed.Msg) :=
  match msg with
  | seller_call_timeout _  => true
  | _=> false
  end.

Definition msg_is_buyer_open_commitment (state : EcommerceFixed.State) (msg : EcommerceFixed.Msg) :=
  match msg with
  | buyer_open_commitment _ _ _  => true
  | _=> false
  end.

Definition get_purchaseId_from_msg (msg : Msg) : option N := 
  match msg with
  | buyer_abort purchaseId
  | buyer_confirm_delivery purchaseId
  | buyer_call_timeout purchaseId
  | buyer_open_commitment purchaseId _ _
  | seller_call_timeout purchaseId
  | seller_accept_contract purchaseId
  | seller_item_was_delivered purchaseId
  | seller_forfeit_dispute purchaseId
  | seller_counter_dispute purchaseId _ => Some purchaseId
  | _ => None
  end.

Definition amount_sent_is_item_value_of_purchase_times_X (X : Z)
  (chain : Chain) (cctx : ContractCallContext) (old_state : EcommerceFixed.State)
  (msg : Msg) (result_opt : option (EcommerceFixed.State * list ActionBody)) :=
  match get_purchaseId_from_msg msg, result_opt with
  | Some purchaseId, Some (_, acts) =>
      match FMap.find purchaseId old_state.(purchases) with
      | Some purchase =>
          match FMap.find purchase.(itemId) old_state.(listings) with
          | Some _item =>
                checker(sum_act_transfer acts =? X * _item.(item_value))
          | _ => checker false (* should never occur *)
          end
      | _ => checker false
      end
  | _, _ => checker false
  end.

(* on [buyer_abort], amount transferred to buyer is equal to item_value in the purchase. *)
(* QuickChick(
  {{ fun state msg => msg_is_buyer_abort state msg }}
  contract_base_addr
  {{ amount_sent_is_item_value_of_purchase_times_X 1 }}
). *)
(* +++ Passed 10000 tests (0 discards) *)

(* on [buyer_open_commitment] the amount transferred to the seller should be twice the item value *)
(* QuickChick(
  {{ fun state msg => msg_is_buyer_open_commitment state msg }}
  contract_base_addr
  {{ amount_sent_is_item_value_of_purchase_times_X 2 }}
). *)
(* +++ Passed 10000 tests (0 discards) *)
(*Definition is_purchase_state (purchase_state_goal : EcommerceFixed.PurchaseState) (chain_state : ChainState) :=
  match get_contract_state EcommerceFixed.State chain_state ecommerce_contract_addr with
  | Some state =>
      match FMap.find purchaseId state.(purchases) with
          | Some purchase => purchase_state_eq purchase.(purchase_state) purchase_state_goal
          | _ => false
      end
  | None => false (* should never occur *)
  end.*)
  
Fixpoint index { A } ( n : nat ) ( l : list A ) : option A :=
  match l with
  | nil => None
  | a :: l' =>
      if beq_nat n O then Some a else index ( pred n ) l'
  end.
  

Definition any {A : Type} (P : A -> bool) (l : list A):=
  negb (forallb (fun a => negb (P a)) l).

  
Definition any_purchase_reaches_state (purchase_state_goal : EcommerceFixed.PurchaseState) (chain_state : ChainState) :=
  match get_contract_state EcommerceFixed.State chain_state ecommerce_contract_addr with
  | Some state => any (fun p => purchase_state_eq p.(purchase_state) purchase_state_goal) (FMap.values state.(purchases))
  | None => false (* should never occur *)
  end.
(* A purchase should be able to reach any [purchase_state] *)

(*QuickChick (ecommerce_chainbuilder ~~> any_purchase_reaches_state EcommerceFixed.requested).
QuickChick (ecommerce_chainbuilder ~~> any_purchase_reaches_state EcommerceFixed.accepted).
QuickChick (ecommerce_chainbuilder ~~> any_purchase_reaches_state EcommerceFixed.rejected).
QuickChick (ecommerce_chainbuilder ~~> any_purchase_reaches_state EcommerceFixed.delivered).
QuickChick (ecommerce_chainbuilder ~~> any_purchase_reaches_state EcommerceFixed.completed).
QuickChick (ecommerce_chainbuilder ~~> any_purchase_reaches_state EcommerceFixed.dispute).
QuickChick (ecommerce_chainbuilder ~~> any_purchase_reaches_state EcommerceFixed.counter).
QuickChick (ecommerce_chainbuilder ~~> any_purchase_reaches_state EcommerceFixed.failed). *)
(* Success - found witness satisfying the predicate! *)


(* TODO? *)
(* If all purchases are of state [failed] [completed] or [rejected] then the contract should
   contain no money. *)
(* NOT TRUE ANY LONGER - We have have "discarded_money". *)
Definition all_purchases_are_finished (cs : ChainState) : bool :=
  match cs.(env_contract_states) ecommerce_contract_addr with
  | Some serialized_state => 
      match deserialize serialized_state with
      | Some state =>
          forallb
          (fun purchase =>
            match (purchase.(purchase_state)) with
            | EcommerceFixed.completed | EcommerceFixed.rejected | EcommerceFixed.failed => true
            | _ => false
            end) (FMap.values state.(purchases))
      | _ => false (* should never occur *)
      end
  | None => true (* No State is found, therefore we say that purchases are finished for simplicity. *)
  end.
  
Definition contract_balance_greater_than_zero (cs : ChainState) :=
  let contract_balance := env_account_balances cs contract_base_addr in
  0 <? contract_balance.
  
(* Either contract balance is greater than zero or all purchases are finished. *)
(* QuickChick({{ fun cs => all_purchases_are_finished cs || contract_balance_greater_than_zero cs}}). *)
(* +++ Passed 10000 tests (0 discards) *)