(* https://docs.soliditylang.org/en/v0.8.13/solidity-by-example.html#id2 *)


Require Import Monads.
Require Import Blockchain.
Require Import Containers.
Require Import Serializable.
Require Import PArith.
Require Import Extras.
From Coq Require Import List.
From Coq Require Import Bool.
From Coq Require Import ZArith.
From Coq Require Import Arith.
Import ListNotations.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Utils Require Import Automation.
From ConCert.Execution Require Import BuildUtils.



Section BlindAuction.
Context `{Base : ChainBase}. 

Set Nonrecursive Elimination Schemes.

Record Bid := build_bid {
  blinded_bid : positive;
  deposit : Amount
}.
MetaCoq Run (make_setters Bid).
Definition Bids := list Bid.

Definition required_true (b: bool) := if b then Some tt else None.
Definition required_false (b: bool) := if b then None else Some tt.


Record State := build_state {
  beneficiary : Address;
  bidding_end : nat;
  reveal_end : nat;
  ended : bool;
  bids : FMap Address Bids;
  highest_bidder : option Address;
  highest_bid : Amount;
  pending_returns : FMap Address Amount
}.


Check FMap.find.
Compute (@FMap.find nat Amount (FMap nat Amount) _ (123%nat) (FMap.empty : FMap nat Amount)).

MetaCoq Run (make_setters State).

Record Setup := build_setup{
  bidding_time : nat;
  reveal_time : nat;
  beneficiary_address : Address
}.

Inductive Msg :=
| bid (blinded_bind : positive)
| reveal (values : list Amount) (fakes : list bool) (secrets : list positive)
| withdraw
| auction_end.


Open Scope Z.

Definition only_before chain time := required_true (chain.(current_slot) <? time)%nat.
Definition only_after chain time := required_true (time <=? chain.(current_slot))%nat.

Definition require_no_money_sent ctx := required_true (ctx.(ctx_amount) =? 0).

(* TEMP HASH FUNCTION - Not cryptographically secure at all! *)
Definition hash_bid (value : Amount) (fake : bool) (secret : positive) :=
    countable.encode (value, fake, secret).
Arguments hash_bid : simpl never.

Definition find_bids_or_empty (key : Address) (map : FMap Address Bids) :=
    match (FMap.find key map) with
    | Some result => result
    | _ => []
    end.
Arguments find_bids_or_empty : simpl never.

Definition find_pending_or_zero (key : Address) (map : FMap Address Amount) :=
    match (FMap.find key map) with  
    | Some pending_amount => pending_amount
    |_ => 0
    end.

Arguments find_pending_or_zero : simpl never.

Definition bid_call chain ctx state blinded_bid : option (State * list ActionBody) :=
    do (only_before chain state.(bidding_end));
    let caller := ctx.(ctx_from) in
    let new_bid := {| blinded_bid := blinded_bid; deposit := ctx.(ctx_amount) |} in
    let previous_caller_bids := find_bids_or_empty caller state.(bids) in
    let updated_caller_bids := previous_caller_bids ++ [new_bid] in
    let updated_bids := FMap.add caller updated_caller_bids state.(bids) in
    Some (state<| bids := updated_bids |>, []).

    
(* Used as an internal function in the contract
   Returns success of bid placement if bid is higher than current highest_bid, and an updated State *)
Definition place_bid (state : State) (bidder : Address) (value : Amount) (fake : bool) (deposit : Amount) : bool * State :=
        let current_pending_returns := state.(pending_returns) in
        let highest_bidder'_opt := state.(highest_bidder) in
        let highest_bid' := state.(highest_bid) in
        (* In the solidity implementation the last two cases are checked outside place_bid. For simplicity it is done here. *)
        match ((value <=? highest_bid') || fake || (deposit <? value)) with
        | true => (false, state)
        | false => 
            let updated_pending_returns :=
              match highest_bidder'_opt with
              | Some highest_bidder' =>
                  let updated_pending_amount := find_pending_or_zero highest_bidder' current_pending_returns + highest_bid' in
                  FMap.add highest_bidder' updated_pending_amount current_pending_returns
              | None => current_pending_returns
              end
            in
            (true, state <| pending_returns := updated_pending_returns|>
                         <| highest_bid := value|>
                         <| highest_bidder := Some bidder |>)
        end.

Definition add_bid_get_state state caller bid : State := 
    let caller_bids := find_bids_or_empty caller state.(bids) in
    let updated_caller_bids := bid::caller_bids in
    let updated_bids := FMap.add caller updated_caller_bids state.(bids) in
    state <| bids := updated_bids |>.

Fixpoint aux_compute_refund (refund : Amount) state caller caller_bids values fakes secrets : option (Amount * State) :=
    match caller_bids, values, fakes, secrets with
    | caller_bid::caller_bids', value::values', fake::fakes', secret::secrets' =>
        if (caller_bid.(blinded_bid) =? hash_bid value fake secret)%positive
        then
          let bid_deposit := caller_bid.(deposit) in
          let (success, updated_state') := place_bid state caller value fake bid_deposit in
          let updated_refund := refund + bid_deposit - (if success then value else 0) in
          let updated_caller_bid := caller_bid <| deposit := 0 |> in
          let updated_state'' := add_bid_get_state updated_state' caller updated_caller_bid in
          aux_compute_refund updated_refund updated_state'' caller caller_bids' values' fakes' secrets'
        else
          let updated_state' := add_bid_get_state state caller caller_bid in (* If hashing is incorrect, return the bid into the state *)
          aux_compute_refund refund updated_state' caller caller_bids' values' fakes' secrets'
    | [], [], [], [] => Some (refund, state)
    | _, _, _, _ => None (* Only happens if the length of the lists in the match are not equal *)
    end.

Definition compute_refund state caller caller_bids values fakes secrets :=
    let updated_bids := FMap.add caller [] state.(bids) in (* Empty the bids *)
    let updated_state := state <| bids := updated_bids |> in
    aux_compute_refund 0 updated_state caller caller_bids values fakes secrets.


Definition reveal_call chain ctx state values fakes secrets: option (State * list ActionBody) :=
    do (only_after chain state.(bidding_end));
    do (only_before chain state.(reveal_end));
    do (require_no_money_sent ctx);
    let caller := ctx.(ctx_from) in
    let caller_bids := find_bids_or_empty caller state.(bids) in
    do to_refund__updated_state <- compute_refund state caller caller_bids values fakes secrets;
    let '(to_refund, updated_state) := to_refund__updated_state in
    Some (updated_state, [act_transfer caller to_refund]).

Definition withdraw_call ctx state : option (State * list ActionBody) := 
    do (require_no_money_sent ctx);
    let caller := ctx.(ctx_from) in
    do withdrawal_amount <- FMap.find caller state.(pending_returns);
    do required_true (0 <? withdrawal_amount);
    let updated_pending_returns := FMap.add caller 0 state.(pending_returns) in
    Some ( state<| pending_returns := updated_pending_returns |>,
           [act_transfer caller withdrawal_amount]).

Definition auction_end_call chain ctx state :=
    do (require_no_money_sent ctx);
    do (only_after chain state.(reveal_end));
    do required_false state.(ended);
    (* The original code in Solidity emits "AuctionEnded" here! Not possible in ConCert at the moment.*)
    Some (state<| ended := true |>, [act_transfer state.(beneficiary) state.(highest_bid)]).

Definition receive (chain : Chain) (ctx : ContractCallContext)
                   (state : State) (msg : option Msg)
                   : option (State * list ActionBody) :=
  match msg with
  | Some (bid blinded_bid) => bid_call chain ctx state blinded_bid
  | Some (reveal values fakes secrets) => reveal_call chain ctx state values fakes secrets
  | Some withdraw => withdraw_call ctx state
  | Some auction_end => auction_end_call chain ctx state
  | _ => None
  end.


Definition init (chain : Chain) (ctx : ContractCallContext) (setup : Setup)
  : option State :=
  let bidding_end := (chain.(current_slot) + setup.(bidding_time))%nat in
  Some {|
    beneficiary := setup.(beneficiary_address);
    bidding_end := bidding_end;
    reveal_end := bidding_end + setup.(reveal_time);
    ended := false;
    bids := FMap.empty;
    highest_bidder := None;
    highest_bid := 0;
    pending_returns := FMap.empty
  |}.

Global Instance Setup_serializable : Serializable Setup :=
  Derive Serializable Setup_rect<build_setup>.

Global Instance Msg_serializable : Serializable Msg :=
  Derive Serializable Msg_rect<bid, reveal, withdraw, auction_end>.

Global Instance Bid_serializable : Serializable Bid :=
  Derive Serializable Bid_rect<build_bid>.

Global Instance State_serializable : Serializable State :=
  Derive Serializable State_rect<build_state>.

Definition contract : Contract Setup Msg State := 
    build_contract init receive.
(*
Section Theories.
From Coq Require Import Psatz.

Check sumZ.
Check ChainTrace.
(*  Definition all_fake_bids_from (from : Address) (state : State) :=
      let from_bids := find_bids_or_empty from state.(bids) in
      filter (fun from_bid =>  ) from_bids *)
Print hash_bid.
(* <--- DELETE? *)
Definition txs_to (to : Address) (txs : list Tx) : list Tx :=
    filter (fun tx => (tx_to tx =? to)%address) txs.
    Arguments txs_to : simpl never.

Definition txs_from (from : Address) (txs : list Tx) : list Tx :=
    filter (fun tx => (tx_from tx =? from)%address) txs.

  Arguments txs_from : simpl never.
Definition transfer_acts_to addr acts :=
    filter (fun a => match a with
                     | act_transfer to _ => (to =? addr)%address
                     | _ => false
                     end) acts.

Arguments transfer_acts_to : simpl never.

Definition money_to
            {bstate_from bstate_to}
            (trace : ChainTrace bstate_from bstate_to)
            caddr addr :=
  sumZ tx_amount (txs_to addr (outgoing_txs trace caddr)) +
  sumZ act_body_amount (transfer_acts_to addr (outgoing_acts bstate_to caddr)).

Definition money_sent_to_contract {bstate_from bstate_to} (trace : ChainTrace bstate_from bstate_to) addr caddr :=
  sumZ tx_amount (txs_from addr (incoming_txs trace caddr)).

Definition reachable_through from to := reachable from /\ inhabited (ChainTrace from to).

(* DELETE? --->*)

Arguments aux_compute_refund : simpl never.
Ltac receive_simpl_step2 :=
  match goal with
  | H: context[receive] |- _ => unfold receive in H; cbn in H
  | |- context[receive] => unfold receive; cbn
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

  Ltac receive_simpl_step :=
    match goal with
    | H: context[receive] |- _ => unfold receive in H; cbn in H
    | H: context[add_bid_get_state] |- _ => unfold add_bid_get_state in H; cbn in H
    | H: context[place_bid] |- _ => unfold place_bid in H; cbn in H
    | H: context[required_true _] |- _ => destruct (required_true _) in H; cbn in H; try congruence
    | H: context[required_false _] |- _ => destruct (required_false _) in H; cbn in H
    | H: context[only_before _ _] |- _=> destruct (only_before _ _); cbn in H
    | H: context[only_after _ _] |- _=> destruct (only_after _ _); cbn in H
    | H: context[find_bids_or_empty _ _] |- _ => destruct (find_bids_or_empty _ _) in H; cbn in H
    | H: context[find_pending_or_zero _ _] |- _ => destruct (find_pending_or_zero _ _) in H; cbn in H
    | H: context[if ?g then _ else _] |- _ => destruct g; cbn in H
    | H: context[FMap.find _ _] |- _ => destruct (FMap.find) in H; cbn in H; try congruence
    end.  

Tactic Notation "receive_simpl" := repeat (receive_simpl_step).

Definition deposit_sum addr state : Amount :=
  let bids_opt := FMap.find addr state.(bids) in
  match bids_opt with
    | Some bids => sumZ deposit bids
    | _ => 0
    end.

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
  receive chain ctx prev_state msg = Some (new_state, new_acts) ->
     prev_state.(bidding_end) = new_state.(bidding_end)
  /\ prev_state.(reveal_end) = new_state.(reveal_end).
Proof.
  intros. destruct msg.
  - destruct m; try solve [receive_simpl; inversion H; auto]
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
(*Theorem reveal_always_greater_than_bidding : forall bstate caddr,
  reachable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  exists cstate,
    contract_state bstate caddr = Some cstate
    /\ (cstate.(bidding_end) <= cstate.(reveal_end))%nat.
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
    instantiate (CallFacts := fun _ _ _ _ => True).
    instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
    unset_all; subst; cbn in *.
    destruct_chain_step; auto.
    destruct_action_eval; auto.
Qed.*)
Print only_after.

Lemma aux_compute_time_eq_state2_TEMP_DELETE_DUPLICATE: forall refund prev_state prev_state' caller caller_bids values fakes secrets to_refund updated_state,
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
(*
Lemma aux_compute_refund_does_not_increase_bids_length : forall caller refund caller_bids prev_state values fakes secrets new_state to_refund,
  aux_compute_refund refund prev_state caller caller_bids values fakes secrets = Some (to_refund, new_state) ->
  (length (find_bids_or_empty caller new_state.(bids)) <= length (find_bids_or_empty caller prev_state.(bids)))%nat.
Proof.
  intros caller refund caller_bids. generalize dependent refund.
  induction caller_bids;
  destruct values eqn:V; destruct fakes eqn:F; destruct secrets eqn:S; intros; try solve [inversion H; auto].
  unfold aux_compute_refund in H.
  destruct ((blinded_bid a =? hash_bid a0 b p)%positive).
  - admit.
  - receive_simpl; apply IHcaller_bids in H. cbn in H.
    + admit.
    + cbn in H.
  - apply IHcaller_bids in H. cbn in H. unfold find_bids_or_empty in H.
     cbn in H. lia. easy.
  - cbn in *. admit.
  - unfold setter_from_getter_Bid_deposit, set_Bid_deposit in *. admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - ad  
  - 
  destruct ((blinded_bid a =? hash_bid a0 b p)%positive).
  - eapply IHcaller_bids in H. cbn in H. admit.
  - receive_simpl.
    +  eapply IHcaller_bids in H.
  - receive_simpl.
  apply (IHcaller_bids prev_state (a0::values) (b::fakes) (p::secrets) new_state to_refund) in H.
  eapply IHcaller_bids in H. receive_simpl; auto.
  - eapply IHcaller_bids in H. admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - eapply IHcaller_bids in H. admit.
  - admit.
  - admit.
  - receive_simpl_step. eapply IHcaller_bids in H. admit.
  - admit. 
  - apply IHcaller_bids in H. cbn in H.  apply IHcaller_bids in H. cbn in H. unfold FMap.add in *. apply H.
  - auto.  try solve [apply IHcaller_bids in H; apply H].
  apply (IHcaller_bids _ (a0::values) (b::fakes) (p::secrets) _ to_refund). apply H.
  -  try solve [inversion H; auto].
(* Length of bids can only get bigger before reveal_end *)
Lemma cannot_place_bids_after_bidding_end : forall chain ctx prev_state msg new_state new_acts addr bids,
  (chain.(current_slot) <? prev_state.(bidding_end))%nat = false -> (* After bidding_end *)
  receive chain ctx prev_state (Some msg) = Some (new_state, new_acts) ->
  (length (find_bids_or_empty addr new_state.(bids)) <= length (find_bids_or_empty addr prev_state.(bids)))%nat.
Proof.
  intros. destruct msg eqn:m; cbn in *; unfold only_before, only_after in *.
  - inversion H. rewrite H in H0. discriminate.
  - do 2 receive_simpl_step. induction find_bids_or_empty in H0.
    + receive_simpl.
      * unfold compute_refund in H0.
      destruct aux_compute_refund eqn:E; try discriminate.
    +
      unfold compute_refund in H0.
      destruct aux_compute_refund eqn:E; try discriminate.
      destruct p as [to_refund updated_state].
      unfold setter_from_getter_State_bids, set_State_bids in *.

      unfold FMap.add in *. cbn in *.
      inversion H0. rewrite <- H2.
      remember (setter_from_getter_State_bids _ _) as prev_state'.
      update setter_from_getter_State_bids in Heqprev_state'.
      inversion Heqprev_state'.
      destruct aux_compute_refund eqn:E; try discriminate.
      destruct p as [to_refund updated_state]. inversion H0. easy.
    unfold compute_refund in *. cbn in *. 
    + unfold compute_refund in *. receive_simpl_step.
      * admit.
      *    auto.
  -  cbn in *. receive_simpl_step. ; auto; inversion H0.
    + 
    receive_simpl_step.
    + receive_simpl_step.
      * inversion H0. unfold setter_from_getter_State_bids, set_State_bids in *. inversion H0. cbn in H0. receive_simpl_step.
      { admit. }
      {} Locate rewrite_environment_equiv. admit.
    + discriminate. 
  rewrite H in H0. receive_simpl.
    + unfold setter_from_getter_State_bids, set_State_bids in *.
Qed.

  
(*
Definition sum_total_bids (inc_calls : list (ContractCallInfo Msg)) (addr : Address) :=
  sumZ call_amount
  (filter (fun inc_call => (inc_call.(call_from) =? addr)%address) /\ call_msg =? ) inc_calls).
Proof.
*)

Definition has_revealed addr inc_calls :=
  existsb (fun inc_call =>
    (inc_call.(call_from) =? addr)%address &&
    match inc_call.(call_msg) with
    | Some (reveal _ _ _) => true
    | _ => false
    end) inc_calls.
  

Definition on_reveal_time chain cstate :=
  (chain.(current_slot) <=? cstate.(bidding_end))%nat &&
  (cstate.(reveal_end) <? chain.(current_slot))%nat.



Definition test2 (incoming_calls : list (ContractCallInfo Msg)) addr :=
  filter (fun inc_call => (inc_call.(call_from) =? addr)%address) incoming_calls.
  
(* There exists a state where a user can withdraw all money if not highest bidder *)
(* Der eksisterer en message, som sætter alle sendte penge til pending. *)
(* All placed bids can be put into pending by some user if not highest bidder *)

Lemma can_withdraw_at_some_point : forall bstate caddr addr addr_deposit_sum,
  reachable bstate ->
  emptyable (chain_state_queue bstate) ->
  (exists cstate, 
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    deposit_sum addr cstate = addr_deposit_sum
  ) ->
  

  receive chain ctx prev_state (Some MSSG values fakes secrets) = Some (new_state, new_acts) ->
  on_reveal_time chain cstate = true ->
  
  reachable bstate ->
  emptyable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  (exists cstate inc_calls, 
       contract_state bstate caddr = Some cstate
    /\ incoming_calls Msg trace caddr = Some inc_calls
  ) ->
  exists bstate',
  
  (exists cstate inc_calls,
     contract_state bstate caddr = Some cstate
  /\ incoming_calls Msg trace caddr = Some inc_calls
  /\ (
      forall addr, 
        cstate.(highest_bidder) <> addr ->  
        2 = 2
     )
  ).
Proof.
  contract_induction; auto.
  - intros. 
  
*)
(* No outgoing transactions before reveal_end *)
(* All placed bids can be put into pending by some user if not highest bidder *)



(* All valid "fake" bids, can be refunded at some point *)
       


(* All bids from addr can be refunded after bidding time has ended, if not highest_bidder *)
(*Lemma all_bids_refunded_if_not_highest_bidder : forall bstate caddr (trace : ChainTrace empty_state bstate) addr,
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  (exists cstate,
      contract_state bstate caddr = Some cstate
  /\ (bstate.(current_slot) <= cstate.(bidding_end))%nat (* Bidding has ended *)
  /\ cstate.(highest_bidder) <> addr (* addr is not highest bidder *)
  /\ money_sent_to_contract trace caddr addr = 0 (* Contract has not sent anything to addr yet *)
  /\ *)

(* All money  *)
(* All bids from addr can be refunded after bidding time has ended, if not highest_bidder *)

(* All bids from addr can be refunded after bidding time has ended, if not highest_bidder *)

(* Can always withdraw pending *)
(* Can never withdraw more money than sent *)

(* Non-highest bidders gets all their money back *)

(* Highest bidder always wins *)

End Theories.
*)  
End BlindAuction.