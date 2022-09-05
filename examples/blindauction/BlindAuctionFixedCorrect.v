From ConCert.Examples.BlindAuction Require Import BlindAuctionFixed.
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

Hint Rewrite N.ltb_lt N.ltb_ge N.leb_le N.leb_gt N.eqb_eq N.eqb_neq
  Nat.ltb_lt Nat.ltb_ge Nat.leb_le Nat.leb_gt 
  Z.leb_le Z.leb_gt Z.eqb_eq
  Bool.orb_true_iff Bool.orb_false_iff
  Bool.andb_true_iff Bool.andb_false_iff
  Bool.negb_false_iff Bool.negb_true_iff : BoolElim.

Ltac receive_simpl_step g :=
  match type of g with
  | context[FMap.find _ ?v] => destruct (FMap.find _ v) eqn:?; cbn in g
  | context[required_true ?cond] => destruct cond eqn:?E; inversion E; cbn in g
  | context[required_false ?cond] => destruct cond eqn:?E; inversion E; cbn in g
  (*| context[compute_refund] => destruct compute_refund as [[? ?] | ]; try discriminate; cbn in g*)

  (* unfolds *)
  | context[only_before _] => unfold only_before in g; cbn in g
  | context[only_after _] => unfold only_after in g; cbn in g
  | context[require_no_money_sent _] => unfold require_no_money_sent in g; cbn in g
  | context[require_no_self_call _] => unfold require_no_self_call in g; cbn in g

  | context[setter_from_getter_State_bids] => unfold setter_from_getter_State_bids in g; cbn in g
  | context[set_State_bids] => unfold set_State_bids in g; cbn in g
  | context[setter_from_getter_State_pending_returns] => unfold setter_from_getter_State_pending_returns in g; cbn in g
  | context[set_State_pending_returns] => unfold set_State_pending_returns in g; cbn in g
  | context[setter_from_getter_State_ended] => unfold setter_from_getter_State_ended in g; cbn in g
  | context[set_State_ended] => unfold set_State_ended in g; cbn in g
  end. 
  
Open Scope Z.
Tactic Notation "receive_simpl" constr(g) := cbn in g; repeat (receive_simpl_step g); try discriminate.

Definition before_bidding_end chain state := (chain.(current_slot) < state.(bidding_end))%nat.
Definition after_reveal_end chain state := (state.(reveal_end) <= chain.(current_slot))%nat.

Lemma bid_call_correct : forall chain ctx prev_state new_state new_acts blinded_bid,
  BlindAuctionFixed.receive chain ctx prev_state (Some (bid blinded_bid)) = Some (new_state, new_acts) ->
  let previous_caller_bids := with_default [] (FMap.find ctx.(ctx_from) prev_state.(bids)) in
  let new_bid := {| blinded_bid := blinded_bid; deposit := ctx.(ctx_amount) |} in
     ctx.(ctx_from) <> ctx.(ctx_contract_address)
  /\ before_bidding_end chain prev_state
  /\ new_state = prev_state <| bids := FMap.add ctx.(ctx_from) (new_bid::previous_caller_bids) prev_state.(bids) |>
  /\ new_acts = [].
Proof.
  intros * receive_some p n. subst p n.
  receive_simpl receive_some. repeat split; try now inversion receive_some.
  - now destruct_address_eq.
  - now apply Nat.ltb_lt in E.
Qed.

Lemma withdraw_call_correct : forall chain ctx prev_state new_state new_acts,
  BlindAuctionFixed.receive chain ctx prev_state (Some withdraw) = Some (new_state, new_acts) ->
     ctx.(ctx_from) <> ctx.(ctx_contract_address)
  /\ ctx.(ctx_amount) = 0
  /\ after_reveal_end chain prev_state
  /\ new_state = prev_state <| pending_returns := FMap.add ctx.(ctx_from) 0 prev_state.(pending_returns) |>
  /\ new_acts = [act_transfer ctx.(ctx_from) (with_default 0 (FMap.find ctx.(ctx_from) prev_state.(pending_returns)))] (*TODO*)
.
Proof.
  intros * receive_some.
  receive_simpl receive_some. repeat split; try now inversion receive_some.
  - now destruct_address_eq.
  - now apply Z.eqb_eq in E1.
  - unfold after_reveal_end. now apply Nat.leb_le.
Qed.

Lemma auction_end_call_correct : forall chain ctx prev_state new_state new_acts,
  BlindAuctionFixed.receive chain ctx prev_state (Some auction_end) = Some (new_state, new_acts) ->
     ctx.(ctx_from) <> ctx.(ctx_contract_address)
  /\ ctx.(ctx_amount) = 0
  /\ after_reveal_end chain prev_state
  /\ new_state = prev_state <| ended := true |>
  /\ new_acts = [act_transfer prev_state.(beneficiary) prev_state.(highest_bid)].
Proof.
  intros * receive_some.
  receive_simpl receive_some. repeat split; cbn in *; try now inversion receive_some.
  - now destruct_address_eq.
  - now apply Z.eqb_eq in E1.
  - unfold after_reveal_end. now apply Nat.leb_le.
Qed.

Ltac receive_simpl_goal_step :=
  match goal with
  | |- context[setter_from_getter_State_bids] => unfold setter_from_getter_State_bids; cbn
  | |- context[set_State_bids] => unfold set_State_bids; cbn
  | |- context[setter_from_getter_State_pending_returns] => unfold setter_from_getter_State_pending_returns; cbn
  | |- context[set_State_pending_returns] => unfold set_State_pending_returns; cbn
  | |- context[setter_from_getter_State_ended] => unfold setter_from_getter_State_ended; cbn
  | |- context[set_State_ended] => unfold set_State_ended; cbn
  end. 

Tactic Notation "receive_simpl_goal" := cbn; repeat (receive_simpl_goal_step; cbn).


(* aux_compute_refund computes correctly for sequence. *)
Lemma compute_refund_correct_for_sequence : forall caller new_state_single refund_single refund new_state prev_state b bids v values f fakes s secrets,
  compute_refund caller 0 prev_state [b] [v] [f] [s] = Some (refund_single, new_state_single) ->
  compute_refund caller refund_single new_state_single bids values fakes secrets = Some (refund, new_state) ->
  compute_refund caller 0 prev_state (b::bids) (v::values) (f::fakes) (s::secrets) = Some (refund, new_state).
Proof.
  intros * H1 H2.
  unfold compute_refund in *; fold compute_refund in *.
  destruct ((b.(blinded_bid) =? hash_bid v f s)%positive).
  - unfold place_bid in *.
    destruct (orb (orb (v <=? highest_bid prev_state)%Z f) (deposit b <? v)%Z);
    cbn in *; inversion H1; easy.
  - easy.
Qed.


(* aux_compute_refund correct for any refund value *)
Lemma compute_refund_correct : forall prev_state refund new_state user bids values fakes secrets start_refund z,
  compute_refund user z prev_state bids values fakes secrets = Some (refund, new_state) ->
  compute_refund user (start_refund + z) prev_state  bids values fakes secrets = Some ((refund + start_refund)%Z, new_state).
Proof.
Admitted.

Lemma compute_refund_correct_refund_on_no_highest_bid : forall prev_state updated_state caller caller_bids values fakes secrets to_refund,
  Forall (fun value => value <= prev_state.(highest_bid)) values ->
  compute_refund caller 0 prev_state caller_bids values fakes secrets = Some (to_refund, updated_state) ->
  to_refund = sumZ deposit caller_bids.
Proof.
Admitted.

Lemma reveal_call_correct_not_highest_bidder : forall chain ctx prev_state new_state new_acts values fakes secrets,
  let caller_bids := with_default [] (FMap.find ctx.(ctx_from) prev_state.(bids)) in
  Forall (fun value => value <= prev_state.(highest_bid)) values ->
  BlindAuctionFixed.receive chain ctx prev_state (Some (reveal values fakes secrets)) = Some (new_state, new_acts) ->
  let transfer_amount := sumZ deposit caller_bids in
  new_acts = [act_transfer ctx.(ctx_from) transfer_amount].
Proof.
Admitted.

End Theories.


