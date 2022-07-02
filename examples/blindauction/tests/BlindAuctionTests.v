

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
    bidding_time := 10;
    reveal_time := 5;
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

(* Sample gChain. *)

Section TestProperties.
  Local Open Scope Z_scope.

(*
  GOAL:
  Prove this
  
  Lemma cannot_place_bids_after_bidding_end : forall chain ctx prev_state msg new_state new_acts addr bids,
  (chain.(current_slot) <? prev_state.(bidding_end))%nat = false -> (* After bidding_end *)
  receive chain ctx prev_state (Some msg) = Some (new_state, new_acts) ->
  (length (find_bids_or_empty addr new_state.(bids)) <= length (find_bids_or_empty addr prev_state.(bids)))%nat.
*)


(*
Definition ok1 := reveal_end_and_bidding_end_does_not_change_on_receive.
Check reveal_end_and_bidding_end_does_not_change_on_receive.

  Definition ok2 chain ctx msg prev_state :=
    match (BlindAuction.receive chain ctx prev_state msg) with
    | Some (new_state, new_acts) =>
        
            (prev_state.(bidding_end) =? new_state.(bidding_end))%nat
          && (prev_state.(reveal_end) =? new_state.(reveal_end))%nat
        
    | _ => false
    end.
Sample gChain.
QuickChick (forAllChainBuilder )

QuickChick (forAllBlindAuctionChainBuilder gBlindAuctionTrace 7 blindauction_chain ok2).
QuickChick (forAll true)
QuickChick (forAll gBlindAuctionTrace )
  Lemma ll chain ctx msg prev_state new_state new_acts :
    ok1 chain ctx msg prev_state new_state new_acts <-> ok2 chain ctx msg prev_state = true.
*)
End TestProperties.