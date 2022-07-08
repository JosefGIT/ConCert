

From ConCert.Examples.BlindAuction Require Import BlindAuction.
From ConCert.Utils Require Import Automation.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ChainedList.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Examples.BlindAuction Require Import BlindAuctionGens.

From ConCert.Examples.BlindAuction Require Import BlindAuctionPrinters.
From Coq Require Import ZArith.
From Coq Require Import List.
Import ListNotations.

Section BlindAuctionTestSetup.

  Definition blind_auction_contract_addr := contract_base_addr.
  Definition seller := creator.
  
  Definition blindauction_setup :=  {|
    bidding_time := 2;
    reveal_time := 3;
    beneficiary_address := seller;
  |}.

  Definition deploy_blindauction := create_deployment 0 BlindAuction.contract blindauction_setup.

  (* Initial ChainBuilder for the property tests. *)
  Definition blindauction_chainbuilder :=
    unpack_result (TraceGens.add_block empty_chain
    [
      build_act creator creator (Blockchain.act_transfer person_1 12);
      build_act creator creator (Blockchain.act_transfer person_2 14);
      build_act creator creator (Blockchain.act_transfer person_3 8);
      build_act creator creator (deploy_blindauction)
    ]).
    
End BlindAuctionTestSetup.

Module TestInfo <: BlindAuctionGensInfo.
  Definition contract_addr := blind_auction_contract_addr.
End TestInfo.
Module MG := BlindAuctionGens.BlindAuctionGens TestInfo.
Import MG.

Module NotationInfo <: TestNotationParameters.
  Definition gAction := gBlindAuctionMsg.
  Definition init_cb := blindauction_chainbuilder.
End NotationInfo.
Module TN := TestNotations NotationInfo.
Import TN.
Locate LocalChainBase.
Sample gChain.

  Local Open Scope Z_scope.

(*
  GOAL:
  Prove this
  
  Lemma cannot_place_bids_after_bidding_end : forall chain ctx prev_state msg new_state new_acts addr bids,
  (chain.(current_slot) <? prev_state.(bidding_end))%nat = false -> (* After bidding_end *)
  receive chain ctx prev_state (Some msg) = Some (new_state, new_acts) ->
  (length (find_bids_or_empty addr new_state.(bids)) <= length (find_bids_or_empty addr prev_state.(bids)))%nat.
*)



(*Definition ok1 := reveal_end_and_bidding_end_does_not_change_on_receive.
Check reveal_end_and_bidding_end_does_not_change_on_receive.*)

Definition ok2 chain ctx msg prev_state :=
  match (BlindAuction.receive chain ctx prev_state msg) with
  | Some (new_state, new_acts) =>
      
          (prev_state.(bidding_end) =? new_state.(bidding_end))%nat
        && (prev_state.(reveal_end) =? new_state.(reveal_end))%nat
      
  | _ => false
  end.

Definition get_chain_height (cb : ChainBuilder) : nat :=
  cb.(builder_env).(chain_height).

Definition reveal_end_and_bidding_end_unchanged (chain : Chain) (cctx : ContractCallContext) (old_state : BlindAuction.State)
                               (msg : Msg) (result_opt : option (BlindAuction.State * list ActionBody)) :=
  match result_opt with
  | Some (new_state, _) =>
      let bidding_end_unchanged := (old_state.(bidding_end) =? new_state.(bidding_end))%nat in
      let reveal_end_unchanged := (old_state.(reveal_end) =? new_state.(reveal_end))%nat in
      checker (bidding_end_unchanged && reveal_end_unchanged)
  | _ => checker false
  end.

(* bidding_end and reveal_end should never change in the State. *)
(* QuickChick ({{fun state msg => true}} blind_auction_contract_addr {{reveal_end_and_bidding_end_unchanged}}). *)

(* At some point (after ended) the contract balance will be 0, i.e. all money gets refunded*)
Definition money_gets_refunded (chain_state : ChainState) :=
  let contract_balance := env_account_balances chain_state contract_base_addr in
  match get_contract_state BlindAuction.State chain_state contract_base_addr with
  | Some state => state.(ended) && (contract_balance =? 0)
  | None => false
  end.
QuickChick (blindauction_chainbuilder ~~> money_gets_refunded).
(* At some point, a user can always withdraw his bids (except if he is the highest bidder) *)
(* TODO:*)
Definition can_refund_at_some_point (chain_state : ChainState):=
  let person_balance := env_account_balances chain_state person_1 in
  match (get_contract_state BlindAuction.State chain_state contract_base_addr)
  | Some state => 
  | None => false
  42.
  fun cs =>
    let contract_balance := env_account_balances cs contract_base_addr in
      match get_contract_state State cs contract_base_addr with
      | Some state => (negb state.(isFinalized)) &&
                      (state.(fundingEnd) <? cs.(current_slot))%nat &&
                      Z.eqb contract_balance 0
      | None => false
      end.
QuickChick (blindauction_chainbuilder ~~>)
Locate ChainBuilder.
Locate forAllChainBuilder.
QuickChick ({{fun state msg => true}} blind_auction_contract_addr {{fun _ _ _ _ _ => true}}).
QuickChick (forAllChainBuilders (fun c => checker true)).
QuickChick (forAllInvalidActions gBlindAuctionMsg ok2).

QuickChick (forAllChainBuilders (fun cb => collect (get_chain_height cb) true)).


QuickChick (forAllChainBuilders gBlindAuctionTrace 7 blindauction_chainbuilder ok2).
QuickChick (forAllBlindAuctionChainBuilder gBlindAuctionTrace 7 blindauction_chain ok2).
QuickChick (forAll true)
QuickChick (forAll gBlindAuctionTrace )
  Lemma ll chain ctx msg prev_state new_state new_acts :
    ok1 chain ctx msg prev_state new_state new_acts <-> ok2 chain ctx msg prev_state = true.
