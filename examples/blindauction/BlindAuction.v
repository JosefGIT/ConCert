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
Arguments aux_compute_refund : simpl never.

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


(* Added +1 on times for easier proofs. *)
Definition init (chain : Chain) (ctx : ContractCallContext) (setup : Setup)
  : option State :=
  let bidding_end := (chain.(current_slot) + setup.(bidding_time) + 1)%nat in
  Some {|
    beneficiary := setup.(beneficiary_address);
    bidding_end := bidding_end;
    reveal_end := bidding_end + setup.(reveal_time) + 1; 
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

End BlindAuction.