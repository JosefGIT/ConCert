From ConCert.Examples.Ecommerce Require Import Ecommerce.
From ConCert.Execution Require Import BuildUtils.
From ConCert.Utils Require Import Automation.
From Coq Require Import ZArith.
From ConCert.Execution Require Import Serializable.
Require Import Blockchain.
Require Import Containers.
Require Import Extras.
From ConCert.Utils Require Import RecordUpdate.
From Coq Require Import Lia.
From Coq Require Import List.
Import ListNotations.
Section Theories.

Context `{Base : ChainBase}. 

Ltac receive_simpl_step g :=
  match type of g with
  | context[get_purchase_option] => unfold get_purchase_option in g; cbn in g
  | context[FMap.find _ _] => destruct (FMap.find _ _) eqn:?; cbn in g
  | context[setter_from_getter_State_purchases] => unfold setter_from_getter_State_purchases in g; cbn in g
  | context[set_State_purchases] => unfold set_State_purchases in g; cbn in g
  | context[setter_from_getter_Purchase_last_block] => unfold setter_from_getter_Purchase_last_block in g; cbn in g
  | context[set_Purchase_last_block] => unfold set_Purchase_last_block in g; cbn in g
  | context[required_true ?cond] => destruct cond eqn:?E; inversion E; cbn in g
  end. 

Tactic Notation "receive_simpl" constr(g) := cbn in g; repeat (receive_simpl_step g); try discriminate.

Ltac receive_simpl_goal_step :=
  match goal with
  | |- context[get_purchase_option] => unfold get_purchase_option
  | |- context[purchase_state_eq] => unfold purchase_state_eq
  | |- context[setter_from_getter_State_purchases] => unfold setter_from_getter_State_purchases
  | |- context[set_State_purchases] => unfold set_State_purchases
  | |- context[setter_from_getter_Purchase_last_block] => unfold setter_from_getter_Purchase_last_block
  | |- context[set_Purchase_last_block] => unfold set_Purchase_last_block
  end. 

Tactic Notation "receive_simpl_goal" := cbn; repeat (receive_simpl_goal_step; cbn).

Open Scope Z.



(* seller and timeout are constant .. *)
(* listings price must never change - not correct in the smart contract implementation! *)
(* Nothing may change in a Purchase except its state and last_block *)
(*Lemma test : forall (z1 z2 z3 : Z),
 z2 = z2 <->
 (z1 = z1 -> z2 = z2).
Proof.
  intros *. split.
  - admit.
  - intros. apply and in H. destruct H.
    +  apply H. destruct H.
    +  Admitted.*)

(* For valid receive buyer_abort, correct conditions hold *)
Lemma buyer_abort_correct : forall chain ctx prev_state new_state new_acts id purchase updated_purchase,
    Ecommerce.receive chain ctx prev_state (Some (buyer_abort id)) = Some (new_state, new_acts) <->
       (FMap.find id prev_state.(purchases) = Some (purchase : Purchase)
    -> ctx.(ctx_from) = purchase.(buyer)
    /\ purchase.(purchase_state) = requested)
    /\ (FMap.find id new_state.(purchases) = Some (updated_purchase)
    -> updated_purchase.(purchase_state) = failed).
    (* Another condition that should be added is that new_acts contains act_transfer with the
       price of the purchase ctx_from. However this does not hold in the smart contract. *)
Proof.
    Admitted.

Lemma purchase_state_eq_correct : forall (state1 state2 : PurchaseState),
  state1 = state2 <-> purchase_state_eq state1 state2 = true.
Proof.
  intros *. split; intros; destruct state1; destruct state2; try discriminate; reflexivity.
Qed.

Lemma seller_accept_contract_correct : forall chain ctx prev_state new_state new_acts id,
  Ecommerce.receive chain ctx prev_state (Some (seller_accept_contract id)) = Some (new_state, new_acts)
  <->
     (exists purchase updated_purchase,
        FMap.find id prev_state.(purchases) = Some purchase
      /\ purchase.(purchase_state) = requested
      /\ FMap.find id new_state.(purchases) = Some updated_purchase
      /\ updated_purchase.(purchase_state) = accepted
      /\ updated_purchase.(last_block) = chain.(current_slot)
      /\ updated_purchase.(commit) = purchase.(commit)
      /\ updated_purchase.(item) = purchase.(item)
      /\ updated_purchase.(seller_bit) = purchase.(seller_bit)
      /\ updated_purchase.(notes) = purchase.(notes)
      /\ updated_purchase.(buyer) = purchase.(buyer)
      /\ new_state.(purchases) = FMap.add id updated_purchase prev_state.(purchases))
  /\ (ctx.(ctx_from) =? prev_state.(seller) = true)%address
  /\ prev_state.(listings) = new_state.(listings)
  /\ prev_state.(seller) = new_state.(seller)
  /\ prev_state.(timeout) = new_state.(timeout)
  /\ new_acts = [].
Proof.
  intros *. split.
  - intros receive_some.
    receive_simpl receive_some.
    remember ({|
      commit := commit p;
      last_block := current_slot chain;
      item := item p;
      seller_bit := seller_bit p;
      notes := notes p;
      purchase_state := accepted;
      buyer := buyer p |})
    as updated_purchase.
    inversion receive_some; clear receive_some. cbn. repeat split.
    exists p, updated_purchase. repeat split; try now inversion Hequpdated_purchase.
    + now apply purchase_state_eq_correct in E.
    + apply FMap.find_add.
  - intros ([purchase [updated_purchase (purchase_found & state_requested & updated_purchase_found &
                updated_state_accepted & block_current & commit_constant & item_constant &
                seller_bit_constant & notes_constant & buyer_constant & purchase_added)]] &
             ctx_from_seller & listings_constant & seller_constant & timeout_constant & no_acts).
    receive_simpl_goal.
    setoid_rewrite purchase_found.
    rewrite state_requested; cbn.
    rewrite ctx_from_seller; cbn.
    rewrite no_acts; cbn.
    rewrite seller_constant, listings_constant, timeout_constant.
    rewrite <- updated_state_accepted, <- block_current, <- commit_constant, <- item_constant,
            <- seller_bit_constant, <- notes_constant, <- buyer_constant.
            auto.
    destruct updated_purchase; destruct new_state; cbn in *.
    now setoid_rewrite <- purchase_added.
Qed.

Lemma buyer_dispute_delivery_correct : forall chain ctx prev_state new_state new_acts id commitment,
  Ecommerce.receive chain ctx prev_state (Some (buyer_dispute_delivery id commitment)) = Some (new_state, new_acts)
  <->
  (exists purchase updated_purchase _item,
     FMap.find id prev_state.(purchases) = Some purchase
  /\ (ctx.(ctx_from) =? purchase.(buyer))%address = true
  /\ purchase.(purchase_state) = delivered
  /\ FMap.find purchase.(item) prev_state.(listings) = Some _item
  /\ _item.(item_value) = ctx.(ctx_amount)
  /\ updated_purchase.(purchase_state) = dispute
  /\ updated_purchase.(last_block) = chain.(current_slot)
  /\ new_state.(purchases) = FMap.add id updated_purchase prev_state.(purchases)
  (* These fields should stay constant *)
  /\ purchase.(commit) = updated_purchase.(commit)
  /\ purchase.(item) = updated_purchase.(item)
  /\ purchase.(seller_bit) = updated_purchase.(seller_bit)
  /\ purchase.(notes) = updated_purchase.(notes)
  /\ purchase.(buyer) = updated_purchase.(buyer))
  /\ prev_state.(listings) = new_state.(listings)
  /\ prev_state.(seller) = new_state.(seller)
  /\ prev_state.(timeout) = new_state.(timeout)
  
  /\ new_acts = []
  .
Proof.
  intros *. split.
  - intros receive_some. receive_simpl receive_some.
    + admit.
    + 

End Theories.