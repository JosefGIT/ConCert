From ConCert.Examples.BlindAuction Require Import BlindAuction.
From ConCert.Execution Require Import BuildUtils.
From ConCert.Utils Require Import Automation.
From Coq Require Import ZArith.
From ConCert.Execution Require Import Serializable.
Require Import Blockchain.
Require Import Containers.
Require Import Extras.
From Coq Require Import Lia.
From Coq Require Import List.
Import ListNotations.
Section Theories.

Context `{Base : ChainBase}. 

Arguments aux_compute_refund : simpl never.
Ltac receive_simpl_step :=
  match goal with
  | H: context[BlindAuction.receive] |- _ => unfold BlindAuction.receive in H; cbn in H
  | |- context[BlindAuction.receive] => unfold BlindAuction.receive; cbn
  | H: context[add_bid_get_state] |- _ => unfold add_bid_get_state in H; cbn in H
  | |- context[add_bid_get_state] => unfold add_bid_get_state; cbn
  | H: context[place_bid] |- _ => unfold place_bid in H; cbn in H
  | |- context[place_bid] => unfold place_bid; cbn
  | H: context[required_true _] |- _ => destruct (required_true _) in H; cbn in H; try congruence
  | |- context[required_true _] => destruct (required_true _); cbn; try congruence
  | H: context[required_false _] |- _ => destruct (required_false _) in H; cbn in H
  | |- context[required_false _] => destruct (required_false _); cbn
  | H: context[only_before _ _] |- _=> destruct (only_before _ _); cbn in H
  | |- context[only_before] => destruct (only_before _ _); cbn
  | H: context[only_after _ _] |- _=> destruct (only_after _ _); cbn in H
  | |- context[only_after] => destruct (only_after _ _); cbn
  | H: context[find_bids_or_empty _ _] |- _ => destruct (find_bids_or_empty _ _) in H; cbn in H
  | |- context[find_bids_or_empty] => destruct (find_bids_or_empty _ _); cbn
  | H: context[find_pending_or_zero _ _] |- _ => destruct (find_pending_or_zero _ _) in H; cbn in H
  | |- context[find_pending_or_zero] => destruct (find_pending_or_zero _ _); cbn
  | H: context[if ?g then _ else _] |- _ => destruct g; cbn in H
  | |- context[if ?g then _ else _] => destruct g; cbn
  | H: context[FMap.find _ _] |- _ => destruct (FMap.find) in H; cbn in H; try congruence
  end. 

Tactic Notation "receive_simpl" := repeat (receive_simpl_step).

Definition total_deposit (addr : Address) (state : BlindAuction.State) : Amount:=
    sumZ deposit (find_bids_or_empty addr state.(bids)). 

Definition bid_has_ended chain state := state.(bidding_end) <? chain.(current_slot)%nat.


(* aux_compute never changes bidding_end or reveal_end *)
Lemma aux_compute_refund_does_not_change_times : forall refund prev_state caller caller_bids values fakes secrets to_refund updated_state,
  aux_compute_refund refund prev_state caller caller_bids values fakes secrets = Some (to_refund, updated_state) ->
     prev_state.(bidding_end) = updated_state.(bidding_end)
  /\ prev_state.(reveal_end) = updated_state.(reveal_end).
Proof.
  intros refund prev_state caller caller_bids; generalize dependent caller. generalize dependent prev_state; generalize dependent refund; 
  induction caller_bids; intros; destruct values; destruct fakes; destruct secrets; try solve [inversion H; auto].
  unfold aux_compute_refund in H. receive_simpl; try solve [apply IHcaller_bids in H; apply H].
Qed.


(* For two states with equal reveal_end and bidding_end, executing aux_compute with those states results in equal bidding_end and reveal_end *)
Lemma aux_compute_time_eq_state: forall refund prev_state prev_state' caller caller_bids values fakes secrets to_refund updated_state,
  aux_compute_refund refund prev_state caller caller_bids values fakes secrets = Some (to_refund, updated_state) ->
     prev_state.(bidding_end) = prev_state'.(bidding_end)
  /\ prev_state.(reveal_end) = prev_state'.(reveal_end) ->
     prev_state'.(bidding_end) = updated_state.(bidding_end)
  /\ prev_state'.(reveal_end) = updated_state.(reveal_end).
Proof.
  intros. apply aux_compute_refund_does_not_change_times in H.
  destruct H as [HB1 HR1], H0 as [HB2 HR2]; split.
  - rewrite <- HB1, HB2. reflexivity.
  - rewrite <- HR1, HR2. reflexivity.
Qed.


Lemma reveal_end_and_bidding_end_does_not_change_on_receive : forall chain ctx msg prev_state new_state new_acts,
  BlindAuction.receive chain ctx prev_state msg = Some (new_state, new_acts) ->
     prev_state.(bidding_end) = new_state.(bidding_end)
  /\ prev_state.(reveal_end) = new_state.(reveal_end).
Proof.
  intros. destruct msg.
  - destruct m; cbn in H; try solve [receive_simpl; inversion H; auto].
    + receive_simpl; try solve [inversion H; auto].
      * unfold compute_refund in H.
        remember (setter_from_getter_State_bids _ _) as prev_state'.
        destruct aux_compute_refund eqn:E; try discriminate.
        destruct p as [to_refund updated_state]. inversion H. rewrite <- H1.
        apply (aux_compute_time_eq_state 0 prev_state' prev_state  (ctx_from ctx) [] values fakes secrets to_refund updated_state); try assumption.
        unfold setter_from_getter_State_bids, set_State_bids in Heqprev_state'. inversion Heqprev_state'. split; reflexivity.
      * unfold compute_refund in H.
        remember (setter_from_getter_State_bids _ _) as prev_state'.
        destruct aux_compute_refund eqn:E; try discriminate.
        destruct p as [to_refund updated_state]. inversion H. rewrite <- H1.
        apply (aux_compute_time_eq_state 0 prev_state' prev_state  (ctx_from ctx) (b :: l) values fakes secrets to_refund updated_state); try assumption.
        unfold setter_from_getter_State_bids, set_State_bids in Heqprev_state'. inversion Heqprev_state'. split; reflexivity.
  - discriminate.
Qed.

(* reveal_end is always greater than bidding_end *)
Theorem reveal_always_greater_than_bidding : forall bstate caddr,
  reachable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  exists cstate,
    contract_state bstate caddr = Some cstate
    /\ (cstate.(bidding_end) < cstate.(reveal_end))%nat.
Proof. intros.
  contract_induction; intros; auto; cbn in *.
  - (* After deployment of contract*)
    inversion init_some. cbn. lia.
  - (* After nonrecursive call *)
    apply reveal_end_and_bidding_end_does_not_change_on_receive in receive_some.
    inversion receive_some. rewrite <- H , <- H0. apply IH.
  - (* After recursive call *)
    apply reveal_end_and_bidding_end_does_not_change_on_receive in receive_some.
    inversion receive_some. rewrite <- H , <- H0. apply IH.
  - (* Proving fact *)
    instantiate (DeployFacts := fun _ _ => True).
    instantiate (CallFacts := fun _ _ _ _  _ => True).
    instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
    unset_all; subst; cbn in *.
    destruct_chain_step; auto.
    destruct_action_eval; auto.
Qed.

(* User can put all his money in pending at some point if he is not the highest bidder.
   Additional requirement for this is that the slot of the chain has not reached bidding_end yet. :
*)


Definition all_hashes_are_satisfied caller_bids values fakes secrets : Prop :=
  let zipped_info := zip (zip (zip caller_bids values) fakes) secrets in
  Forall (fun '(caller_bid, value, fake, secret) => (caller_bid.(blinded_bid) =? hash_bid value fake secret)%positive = true) zipped_info.

(*Lemma can_always_retrieve_all_bids_if_not_highest_bidder :
    forall bstate (user caddr creator : Address) (reward deposit : Amount) values fakes secrets,
    address_is_contract creator = false ->
    address_is_contract user = false ->
    (reward >= 0)%Z -> (* Necessary to forward_time *)
    reachable bstate ->
    emptyable (chain_state_queue bstate) ->
    (exists cstate,
           env_contracts bstate caddr = Some (BlindAuction.contract : WeakContract)
        /\ env_contract_states bstate caddr = Some ((@serialize State _) cstate)
        /\ bstate.(current_slot) <= cstate.(bidding_end) (* Additional requirement for this contract. Should be fixed! *)
        /\ all_hashes_are_satisfied (find_bids_or_empty user cstate.(bids)) values fakes secrets
        /\ deposit = total_deposit user cstate
    ) ->
    (exists bstate',
           reachable_through bstate bstate'
        /\ emptyable (chain_state_queue bstate')
        /\ (exists cstate',
                   env_contracts bstate' caddr = Some (BlindAuction.contract : WeakContract)
                /\ deposit = find_pending_or_zero user cstate'.(pending_returns)
           )
    ).
Proof.
*)

(* Cannot call "bid" when bid_ended <= current_slot *)
Lemma cannot_bid_when_bid_ended : forall chain ctx prev_state new_state msg new_acts blinded_bid,
  prev_state.(bidding_end) <= chain.(current_slot) ->
  BlindAuction.receive chain ctx prev_state msg = Some (new_state, new_acts) ->
  msg <> Some (BlindAuction.bid blinded_bid).
Proof.
  intros * timeH receiveH.
  destruct msg as [m | ]; auto; destruct m; auto.
  cbn in *. unfold only_before in *. destruct (chain.(current_slot) <? prev_state.(bidding_end)) eqn:E; auto.
  apply leb_complete in E. lia.
Qed.

(* If pending_returns is empty, calling withdraw should return None. *)
Lemma pending_returns_empty_withdraw_returns_none : forall chain ctx prev_state,
  prev_state.(pending_returns) = FMap.empty -> 
  BlindAuction.receive chain ctx prev_state (Some withdraw) = None.
Proof.
  intros * pending_returns_empty. cbn.
  rewrite pending_returns_empty. rewrite FMap.find_empty.
  receive_simpl; easy.
Qed.


(* No pending returns before bidding_end *)
Lemma no_pending_returns_before_bidding_end : forall caddr bstate,
  reachable bstate ->  
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  (exists cstate,
      contract_state bstate caddr = Some cstate
   /\ (bstate.(current_slot) < cstate.(bidding_end) -> cstate.(pending_returns) = FMap.empty)
  ).
Proof.
  contract_induction; intros; cbn in *; auto.
    (* Instantiate BlockFacts and use the fact in the proof. *)
  - instantiate (AddBlockFacts := fun _ old_slot _ _ new_slot _ => old_slot < new_slot ).
    subst AddBlockFacts. cbn in facts. apply IH. lia.
  - unfold BlindAuction.init in *. now inversion init_some.
  - pose proof (reveal_end_and_bidding_end_does_not_change_on_receive _ _ _ _ _ _ receive_some) as [same_bid same_reveal].
    destruct msg as [m |]; try discriminate. destruct m eqn:MSG.
    + receive_simpl; inversion receive_some; cbn in *;
      subst; auto.
    + unfold BlindAuction.receive, BlindAuction.reveal_call in *.
      unfold only_after in *.
      destruct (prev_state.(bidding_end) <=? chain.(current_slot)) eqn:OA; try discriminate.
      apply leb_complete in OA. rewrite same_bid in OA. lia.
    + rewrite <- same_bid in H. apply IH in H.
      pose proof (pending_returns_empty_withdraw_returns_none chain ctx prev_state H).
      rewrite H0 in receive_some. discriminate.
    + receive_simpl; try discriminate.
      inversion receive_some; cbn in *.
      destruct H1. cbn in *. auto.
  (* Copy-pasted from previous proof. Any easier way of doing this? *)
  - pose proof (reveal_end_and_bidding_end_does_not_change_on_receive _ _ _ _ _ _ receive_some) as [same_bid same_reveal].
    destruct msg as [m |]; try discriminate. destruct m eqn:MSG.
    + receive_simpl; inversion receive_some; cbn in *;
      subst; auto.
    + unfold BlindAuction.receive, BlindAuction.reveal_call in *.
      unfold only_after in *.
      destruct (prev_state.(bidding_end) <=? chain.(current_slot)) eqn:OA; try discriminate.
      apply leb_complete in OA. rewrite same_bid in OA. lia.
    + rewrite <- same_bid in H. apply IH in H.
      pose proof (pending_returns_empty_withdraw_returns_none chain ctx prev_state H).
      rewrite H0 in receive_some. discriminate.
    + receive_simpl; try discriminate.
      inversion receive_some; cbn in *.
      destruct H1. cbn in *. auto.
  - instantiate (DeployFacts := fun _ _ => True).
    instantiate (CallFacts := fun _ _ _ _  _ => True).
    unset_all; subst; cbn in *.
    destruct_chain_step; auto.
    + destruct valid_header; auto.
    + destruct_action_eval; auto.
Qed.

(* No outgoing acts before bidding has ended! *)
Lemma no_outgoing_acts_before_bidding_end : forall caddr bstate,
  reachable bstate ->  
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  (exists cstate,
      contract_state bstate caddr = Some cstate
   /\ (bstate.(current_slot) < cstate.(bidding_end) -> outgoing_acts bstate caddr = [])
  ).
Proof.
  contract_induction; 
  only 1: instantiate (CallFacts := fun bstate _ cstate _ _ =>
    cstate.(bidding_end) < cstate.(reveal_end) /\
    (bstate.(current_slot) < cstate.(bidding_end) ->
    cstate.(pending_returns) = FMap.empty));
  intros; cbn in *; auto.
  - apply IH in H. discriminate.
  - pose proof (reveal_end_and_bidding_end_does_not_change_on_receive _ _ _ _ _ _ receive_some) as [same_bid same_reveal].
    destruct msg as [m |]; try discriminate. destruct m; cbn in *.
    + receive_simpl; inversion receive_some; destruct H1; cbn in *; easy.
    + unfold only_after in *.
      destruct (prev_state.(bidding_end) <=? chain.(current_slot)) eqn:E; try discriminate.
      apply leb_complete in E. lia.
    + subst CallFacts. cbn in *. destruct facts as [fact1 fact2]. rewrite fact2 in receive_some; try easy.
      rewrite FMap.find_empty in receive_some. receive_simpl; try discriminate.
    + subst CallFacts. cbn in *. destruct facts as [fact1 fact2].
      unfold only_after in *. destruct (prev_state.(reveal_end) <=? chain.(current_slot)) eqn:E; cbn in *.
      * cbn in *. apply leb_complete in E. lia.
      * cbn in *. receive_simpl; try discriminate.
  - pose proof (reveal_end_and_bidding_end_does_not_change_on_receive _ _ _ _ _ _ receive_some) as [same_bid same_reveal].
    rewrite <- same_bid in H.
    now apply IH in H.
  - apply IH in H. rewrite H in perm.
    now apply Permutation.Permutation_nil in perm.
  - instantiate (DeployFacts := fun _ _ => True).
    instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
    subst CallFacts.
    unset_all; subst;
    destruct_chain_step; auto.
    destruct_action_eval; auto.
    intros * contract_deployed H. split.
    + apply reveal_always_greater_than_bidding in contract_deployed as (cstate' & H1 & H2); try easy.
    cbn in *. rewrite deployed_state in H, H1. rewrite H in H1. inversion H1.
    apply H2.
    + apply no_pending_returns_before_bidding_end in contract_deployed as (cstate' & H1 & H2); try easy.
    cbn in *. rewrite deployed_state in H, H1. rewrite H in H1. inversion H1.
    apply H2.
Qed.

End Theories.