From ConCert.Examples.BlindAuction Require Import BlindAuction.
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

Ltac receive_simpl_step2 g :=
  match type of g with
  | context[BlindAuction.receive] => unfold BlindAuction.receive in g; cbn in g
  | context[add_bid_get_state] => unfold add_bid_get_state in g; cbn in g
  | context[place_bid] => unfold place_bid in g; cbn in g
  | context[required_true _] => destruct (required_true _); cbn in g; try congruence
  | context[required_false _] => destruct (required_false _); cbn in g
  | context[only_before] => destruct (only_before _ _); cbn in g
  | context[only_after] => destruct (only_after _ _); cbn in g
  | context[find_bids_or_empty] => destruct (find_bids_or_empty _ _); cbn in g
  | context[find_pending_or_zero] => destruct (find_pending_or_zero _ _); cbn in g
  | context[require_no_money_sent] => destruct (require_no_money_sent _); cbn in g
  | context[if ?g then _ else _] => destruct g; cbn in g
  end. 

Tactic Notation "receive_simpl2" constr(g) := cbn in g; repeat (receive_simpl_step2 g).


Open Scope Z.

Definition all_hashes_are_satisfied caller_bids values fakes secrets : Prop :=
  let zipped_info := zip (zip (zip caller_bids values) fakes) secrets in
  Forall (fun '(caller_bid, value, fake, secret) => (caller_bid.(blinded_bid) =? hash_bid value fake secret)%positive = true) zipped_info.


Definition total_deposit (addr : Address) (state : BlindAuction.State) : Amount:=
    sumZ deposit (find_bids_or_empty addr state.(bids)). 

Definition bid_has_ended chain state := (state.(bidding_end) <? chain.(current_slot))%nat.

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
Lemma reveal_always_greater_than_bidding : forall bstate caddr,
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

Definition transfer_acts_to addr acts :=
    filter (fun a => match a with
                     | act_transfer to _ => (to =? addr)%address
                     | _ => false
                     end) acts.

Definition transfer_acts_amount_sum_to addr acts :=
  let transfer_acts_to_addr := transfer_acts_to addr acts in
  sumZ (fun ta => act_body_amount ta) transfer_acts_to_addr.

(* For aux_compute with singleton input arrays, the refund should be deposit of the bid if not highest bidder *)
Lemma aux_compute_for_single_bid_refunds_not_highest_bid : forall user prev_state b v f s refund new_state,
  find_bids_or_empty user prev_state.(bids) = [b] ->
  (v <=? prev_state.(highest_bid))%Z = true ->
  all_hashes_are_satisfied [b] [v] [f] [s] ->
  aux_compute_refund 0 prev_state user [b] [v] [f] [s] = Some (refund, new_state) ->
  (refund)%Z = b.(deposit).
Proof.
  intros * user_bids not_highest hashes_satisfied aux_some.
  inversion hashes_satisfied. clear H2 H H0 x l.
  unfold aux_compute_refund in *. rewrite H1 in aux_some.
  unfold place_bid in *. rewrite not_highest in aux_some.
  cbn in *. inversion aux_some. cbn in *. easy. 
Qed.

(* For aux_compute with singleton input arrays, the refund should be deposit-value of the bid if highest bidder, bid is not fake, and the value is valid *)
Lemma aux_compute_for_single_bid_refunds_highest_bid : forall user prev_state b v f s refund new_state,
  find_bids_or_empty user prev_state.(bids) = [b] ->
  (v <=? prev_state.(highest_bid))%Z = false /\ f = false /\ (b.(deposit) <? v = false)%Z->
  all_hashes_are_satisfied [b] [v] [f] [s] ->
  aux_compute_refund 0 prev_state user [b] [v] [f] [s] = Some (refund, new_state) ->
  refund = (b.(deposit) - v)%Z.
Proof.
  intros * user_bids (is_highest & not_fake & invalid_value) hashes_satisfied aux_some.
  inversion hashes_satisfied. clear H2 H H0 x l.
  unfold aux_compute_refund in *. rewrite H1 in aux_some.
  unfold place_bid in *. rewrite is_highest, not_fake, invalid_value in aux_some.
  cbn in *. inversion aux_some. easy. 
Qed.

(* aux_compute_refund computes correctly for sequence. *)
Lemma aux_compute_refund_correct_for_sequence : forall user new_state_single refund_single refund new_state prev_state b bids v values f fakes s secrets,
  aux_compute_refund 0 prev_state user [b] [v] [f] [s] = Some (refund_single, new_state_single) ->
  aux_compute_refund refund_single new_state_single user bids values fakes secrets = Some (refund, new_state) ->
  aux_compute_refund 0 prev_state user (b::bids) (v::values) (f::fakes) (s::secrets) = Some (refund, new_state).
Proof.
  intros * H1 H2.
  unfold aux_compute_refund in *; fold aux_compute_refund in *.
  destruct ((b.(blinded_bid) =? hash_bid v f s)%positive).
  - unfold place_bid in *.
    destruct (orb (orb (v <=? highest_bid prev_state)%Z f) (deposit b <? v)%Z);
    cbn in *; inversion H1; easy.
  - easy.
Qed.
  
(*aux_compute_refund 0 prev_state user (b::bids) (v::values) (f::fakes) (s::secrets) = Some (refund, new_state) ->
aux_compute_refund 0 prev_state user bids values fakes secrets = Some (refund, new_state) ->*)

(* aux_compute_refund correct for any refund value *)
Lemma aux_compute_refund_correct : forall prev_state refund new_state user bids values fakes secrets start_refund z,
  aux_compute_refund z prev_state user bids values fakes secrets = Some (refund, new_state) ->
  aux_compute_refund (start_refund + z) prev_state user bids values fakes secrets = Some ((refund + start_refund)%Z, new_state).
Proof.
  intros * H.
  generalize dependent z;
  generalize dependent prev_state;
  generalize dependent secrets;
  generalize dependent fakes;
  generalize dependent values.
  induction bids as [|b bids'];
  destruct values as [|v values'];
  destruct fakes as [|f fakes'];
  destruct secrets as [|s secrets'];
  intros * H;
  try discriminate; unfold aux_compute_refund in *. 
  - inversion H. easy.
  - fold aux_compute_refund in *.
    destruct (b.(blinded_bid) =? hash_bid v f s)%positive; try easy.
    cbn in *. unfold place_bid in *.
    destruct (orb (orb (v <=? highest_bid prev_state)%Z f) (deposit b <? v)%Z);
    cbn in *.
    + remember (add_bid_get_state prev_state user
    (setter_from_getter_Bid_deposit (fun _ : Amount => 0%Z) b)) as updated_state.
    rewrite <- Zminus_0_l_reverse in H.
    Locate add_assoc.
    rewrite <- (Z.add_assoc start_refund z b.(deposit)).
    rewrite <- Zminus_0_l_reverse.
    now apply (IHbids' values' fakes' secrets' updated_state (z + b.(deposit))%Z).
    + remember (add_bid_get_state
      (setter_from_getter_State_highest_bidder
        (fun _ : option Address => Some user)
        (setter_from_getter_State_highest_bid (fun _ : Amount => v)
            (setter_from_getter_State_pending_returns
              (fun _ : FMap Address Amount =>
                match highest_bidder prev_state with
                | Some highest_bidder' =>
                    FMap.add highest_bidder'
                      (find_pending_or_zero highest_bidder'
                        (pending_returns prev_state) + 
                      highest_bid prev_state)%Z (pending_returns prev_state)
                | None => pending_returns prev_state
                end) prev_state))) user
      (setter_from_getter_Bid_deposit (fun _ : Amount => 0%Z) b)) as updated_state.
      assert (rewriting : (start_refund + z + b.(deposit) - v) = start_refund + (z + b.(deposit) - v )). { lia. }
      rewrite rewriting.
      now apply (IHbids' values' fakes' secrets' updated_state (z + b.(deposit) - v)%Z).
Qed.

(* When calling reveal with no highest_bid and correct hashes for all bids, reveal should transfer the sum of the deposit from the bids to the caller (user).  *)
Lemma compute_refund_correct_refund_on_no_highest_bid : forall prev_state updated_state caller caller_bids values fakes secrets,
  all_hashes_are_satisfied caller_bids values fakes secrets ->
  Forall (fun val => (val <=? prev_state.(highest_bid))%Z = true) values ->
  compute_refund prev_state caller caller_bids values fakes secrets = Some (sumZ deposit caller_bids, updated_state).
Proof.
  Admitted.

(* When calling reveal with no highest_bid and correct hashes for all bids, reveal should transfer the sum of the deposit from the bids to the caller (user).  *)
Lemma reveal_transfers_money_correctly_on_no_highest_bid : forall chain ctx prev_state new_state new_acts values fakes secrets,
  let user := ctx.(ctx_from) in
  let user_bids := (find_bids_or_empty user prev_state.(bids)) in
  BlindAuction.receive chain ctx prev_state (Some (reveal values fakes secrets)) = Some (new_state, new_acts) ->
  Forall (fun val => (val <=? prev_state.(highest_bid))%Z = true) values ->
  all_hashes_are_satisfied user_bids values fakes secrets ->
  new_acts = [act_transfer user (sumZ deposit user_bids)].
Proof.
  Admitted.

(* Cannot call "bid" when bid_ended <= current_slot *)
Lemma cannot_bid_when_bid_ended : forall chain ctx prev_state new_state msg new_acts blinded_bid,
  (prev_state.(bidding_end) <= chain.(current_slot))%nat ->
  BlindAuction.receive chain ctx prev_state msg = Some (new_state, new_acts) ->
  msg <> Some (BlindAuction.bid blinded_bid).
Proof.
  intros * timeH receiveH.
  destruct msg as [m | ]; auto; destruct m; auto.
  cbn in *. unfold only_before in *. destruct (chain.(current_slot) <? prev_state.(bidding_end))%nat eqn:E; auto.
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
   /\ ((bstate.(current_slot) < cstate.(bidding_end))%nat -> cstate.(pending_returns) = FMap.empty)
  ).
Proof.
  contract_induction; intros; cbn in *; auto.
    (* Instantiate BlockFacts and use the fact in the proof. *)
  - instantiate (AddBlockFacts := fun _ old_slot _ _ new_slot _ => (old_slot < new_slot)%nat ).
    subst AddBlockFacts. cbn in facts. apply IH. lia.
  - unfold BlindAuction.init in *. now inversion init_some.
  - pose proof (reveal_end_and_bidding_end_does_not_change_on_receive _ _ _ _ _ _ receive_some) as [same_bid same_reveal].
    destruct msg as [m |]; try discriminate. destruct m eqn:MSG.
    + receive_simpl; inversion receive_some; cbn in *;
      subst; auto.
    + unfold BlindAuction.receive, BlindAuction.reveal_call in *.
      unfold only_after in *.
      destruct (prev_state.(bidding_end) <=? chain.(current_slot))%nat eqn:OA; try discriminate.
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
      destruct (prev_state.(bidding_end) <=? chain.(current_slot))%nat eqn:OA; try discriminate.
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
   /\ ((bstate.(current_slot) < cstate.(bidding_end))%nat -> outgoing_acts bstate caddr = [])
  ).
Proof.
  contract_induction; 
  only 1: instantiate (CallFacts := fun bstate _ cstate _ _ =>
    (cstate.(bidding_end) < cstate.(reveal_end))%nat /\
    ((bstate.(current_slot) < cstate.(bidding_end))%nat ->
    cstate.(pending_returns) = FMap.empty));
  intros; cbn in *; auto.
  - apply IH in H. discriminate.
  - pose proof (reveal_end_and_bidding_end_does_not_change_on_receive _ _ _ _ _ _ receive_some) as [same_bid same_reveal].
    destruct msg as [m |]; try discriminate. destruct m; cbn in *.
    + receive_simpl; inversion receive_some; destruct H1; cbn in *; easy.
    + unfold only_after in *.
      destruct (prev_state.(bidding_end) <=? chain.(current_slot))%nat eqn:E; try discriminate.
      apply leb_complete in E. lia.
    + subst CallFacts. cbn in *. destruct facts as [fact1 fact2]. rewrite fact2 in receive_some; try easy.
      rewrite FMap.find_empty in receive_some. receive_simpl; try discriminate.
    + subst CallFacts. cbn in *. destruct facts as [fact1 fact2].
      unfold only_after in *. destruct (prev_state.(reveal_end) <=? chain.(current_slot))%nat eqn:E; cbn in *.
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