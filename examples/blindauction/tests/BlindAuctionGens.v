
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.Test Require Import QCTest.
Import MonadNotation.
From Coq Require Import ZArith.
From Coq Require Import List.
Require Import BinPos PeanoNat.
Import ListNotations.
From ConCert.Examples.BlindAuction Require Import BlindAuction.
Import Containers.
(* Necessary to pass a contract adddress from the BlindAuctionTests file. *)
Module Type BlindAuctionGensInfo.
  Parameter contract_addr : Address.
  Parameter max_init_money_nat : nat.
End BlindAuctionGensInfo.


Module BlindAuctionGens (Info : BlindAuctionGensInfo).
Import Info.

Definition Env := Environment.
Open Scope Z_scope.


(*Definition gRandom_256bit_positive : G positive :=
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
  gPositive 256%nat.*)

Check 1.

(* A constant "fake secret" is used to later be able to extract the input of the hash by trying all possible inputs *)
Definition fake_secret := 42%positive.


Fixpoint compute_correct_values_from_hashes_aux (addr : Address) (hash : positive) (amount : nat) : (Amount * bool * positive) :=
  let amount_Z := Z_of_nat amount in
  match amount with
  | S amount' =>
      let hash_faketrue := BlindAuction.hash_bid amount_Z true fake_secret in
      let hash_fakefalse := BlindAuction.hash_bid amount_Z false fake_secret in
      if (hash_faketrue =? hash)%positive then (amount_Z, true, fake_secret) else
      if (hash_fakefalse =? hash)%positive then (amount_Z, false, fake_secret) else
      compute_correct_values_from_hashes_aux addr hash amount'
  | _ => (0, false, fake_secret)
  end.

Fixpoint compute_correct_values_from_hashes (addr : Address) (hashes : list positive) : ((list Amount) * (list bool) * (list positive)):=
  match hashes with
  | hash'::hashes' =>
    let '(value, fake, secret) := (compute_correct_values_from_hashes_aux addr hash' max_init_money_nat) in
    let '(values, fakes, secrets) := compute_correct_values_from_hashes addr hashes' in
    (value::values, fake::fakes, secret::secrets)
  | _ => ([], [], [])
  end.
  
Definition arbitrary_caller : G Address := oneOf [returnGen person_1; returnGen person_2; returnGen person_3].
Check arbitrary_caller.

Definition caller_has_pending_money_or_none (state : BlindAuction.State) (caller : Address) : option Address :=
  match FMap.find caller state.(pending_returns) with
      | Some amount =>
          if 0 <? amount
          then Some caller
          else None
      | _ => None
      end.

Definition caller_with_pending_money (state : BlindAuction.State) : GOpt Address :=
  backtrack [
    (1%nat, returnGen (caller_has_pending_money_or_none state person_1));
    (1%nat, returnGen (caller_has_pending_money_or_none state person_2));
    (1%nat, returnGen (caller_has_pending_money_or_none state person_3))
  ]
.

Definition caller_with_money (env : Env) (caller : Address) : option (Address * Amount) :=
  let caller_balance := env.(env_account_balances) caller in
  if 0 <? caller_balance
  then Some (caller, caller_balance)
  else None.

Definition gCaller_with_money (env : Env) : GOpt (Address * Amount):=
  backtrack [
    (1%nat, returnGen (caller_with_money env person_1));
    (1%nat, returnGen (caller_with_money env person_2));
    (1%nat, returnGen (caller_with_money env person_3))
  ].

Definition gBlindAuctionMsg (env : Env) : GOpt Action :=
    let call caller amount msg :=
      returnGenSome {|
          act_origin := caller;
          act_from := caller;
          act_body := act_call contract_addr amount (@serialize BlindAuction.Msg BlindAuction.Msg_serializable msg)
      |} in
    state <- returnGen (get_contract_state BlindAuction.State env contract_addr);;
    let current_slot := env.(env_chain).(current_slot) in
    backtrack[
      (1%nat,
      (* bid *)
      if (state.(bidding_end) <=? current_slot)%nat && (current_slot <? state.(reveal_end))%nat
      then
        returnGen None
      else
        '(caller, caller_balance) <- gCaller_with_money env;;
        deposit <- choose (1, caller_balance);;
        (* Slightly more than 10% chance of making an invalid bid (if bid is strictly greater than deposit) *)
        actual_bid <- freq [(9%nat, choose (1, deposit)); (1%nat, choose (deposit, caller_balance))];;
        fake <- freq [(1%nat, returnGen true); (3%nat, returnGen false)];;
        let secret := fake_secret in
        let secret_bid := hash_bid actual_bid fake secret in
        call caller deposit (bid secret_bid)
      );
      (* reveal *)
      (1%nat,
      caller <- arbitrary_caller;;
      let caller_bids := BlindAuction.find_bids_or_empty caller state.(bids) in
      let caller_blinded_bids := map (fun bid => bid.(blinded_bid)) caller_bids in
      let '(values, fakes, secrets) := compute_correct_values_from_hashes caller caller_blinded_bids in
      call caller 0 (reveal values fakes secrets)
      );
      (* withdraw *)
      (1%nat,
      caller <- caller_with_pending_money state;;
      call caller 0 withdraw
      );
      (* auction_end *)
      (1% nat,
      if (current_slot <? state.(reveal_end))%nat
      then
        returnGen None
      else
        caller <- arbitrary_caller;;
        call caller 0 auction_end
      )
    ].
    

(*Definition gBlindAuctionTrace cb length :=
  gChain cb (fun env _ => gBlindAuctionMsg env) length 1 1.
  
Definition forAllBlindAuctionChainBuilder `{Show ChainBuilder} gBlindAuctionTrace length (cb : ChainBuilder) := 
  forAllChainBuilder length cb gBlindAuctionTrace.

*)
End BlindAuctionGens.