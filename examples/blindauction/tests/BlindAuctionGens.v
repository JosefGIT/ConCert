
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.Test Require Import QCTest.
Import MonadNotation.
From Coq Require Import ZArith.
From Coq Require Import List.
Require Import BinPos PeanoNat.
Import ListNotations.
From ConCert.Examples.BlindAuction Require Import BlindAuction.

(* Necessary to pass a contract adddress from the BlindAuctionTests file. *)
Module Type BlindAuctionGensInfo.
  Parameter contract_addr : Address.
End BlindAuctionGensInfo.


Module BlindAuctionGens (Info : BlindAuctionGensInfo).
Import Info.

Definition Env := Environment.
Open Scope Z_scope.


Print Msg.
Print positive.

Definition gRandom_256bit_positive : G positive :=
  let fix gPositive size := 
    match size with
    | S size' =>
          random_bit <- gPositive size';;
          oneOf [
            returnGen (xI random_bit);
            returnGen (xO random_bit)
          ]
    | _ => returnGen xH
    end in
  gPositive 256%nat.


Definition gBlindAuctionMsg (env : Env): GOpt Action := 
    let call caller amount msg :=
      returnGenSome {|
          act_origin := caller;
          act_from := caller;
          act_body := act_call contract_addr amount (@serialize BlindAuction.Msg BlindAuction.Msg_serializable msg)
        |} in
    state <- returnGen (get_contract_state BlindAuction.State env contract_addr);;
    caller <- oneOf [returnGen person_1; returnGen person_2; returnGen person_3; returnGen creator];;
    let caller_balance := env.(env_account_balances) caller in
    backtrack [
        (* bid *)
        (1%nat,
        if caller_balance <? 1
        then
          returnGen None
        else
        deposit <- choose (1, caller_balance);;
        (* Slightly more than 10% chance of making an invalid bid (if bid is strictly greater than deposit) *)
        actual_bid <- freq [(9%nat, choose (1, deposit)); (1%nat, choose (deposit, caller_balance))];;
        fake <- freq [(1%nat, returnGen true); (3%nat, returnGen false)];;
        secret <- gRandom_256bit_positive;;
        let secret_bid := hash_bid actual_bid fake secret in
          call caller deposit (bid secret_bid)
        );
        (1%nat,
          call caller 0 withdraw
        )
    ].
    

(*Definition gBlindAuctionTrace cb length :=
  gChain cb (fun env _ => gBlindAuctionMsg env) length 1 1.
  
Definition forAllBlindAuctionChainBuilder `{Show ChainBuilder} gBlindAuctionTrace length (cb : ChainBuilder) := 
  forAllChainBuilder length cb gBlindAuctionTrace.

*)
End BlindAuctionGens.