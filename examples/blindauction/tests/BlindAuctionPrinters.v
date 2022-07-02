From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Examples.BlindAuction Require Import BlindAuction.

Require Import PArith.
Local Open Scope string_scope.

(* TODO! *)
Instance showPositive : Show positive :=
{
  show (pos : positive) :=  match pos with | _ => "s" end
}.

Derive Show for Msg.
Instance showSetup : Show Setup :=
{
    show setup :=
           "Setup{"
        ++ "bidding_time: " ++ show setup.(bidding_time) ++ sep
        ++ "reveal_time: " ++ show setup.(reveal_time)  ++ sep
        ++ "beneficiary_address: " ++ show setup.(beneficiary_address)
        ++ "}"
}.

Instance showBid : Show Bid :=
{
  show bid := 
        "Bid{"
     ++ "blinded_bid: " ++ show bid.(blinded_bid) ++ sep
     ++ "deposit: " ++ show bid.(deposit)
     ++ "}"
}.
Instance showState : Show State :=
{
    show state := 
        "State{"
     ++ "beneficiary: " ++ show state.(beneficiary) ++ sep
     ++ "bidding_end: " ++ show state.(bidding_end) ++ sep
     ++ "reveal_end: " ++ show state.(reveal_end) ++ sep
     ++ "ended: " ++ show state.(ended) ++ sep
     ++ "bids: " ++ show state.(bids) ++ sep
     ++ "highest_bidder: " ++ show state.(highest_bidder) ++ sep
     ++ "highest_bid: " ++ show state.(highest_bid) ++ sep
     ++ "pending_returns: " ++ show state.(pending_returns) 
     ++ "}"
}.

Instance showSerializedMsg : Show SerializedValue :=
  Derive Show Msg < Msg, Setup >.
  

