From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Examples.FA2 Require Import FA2Token.
From ConCert.Examples.FA2 Require Import FA2LegacyInterface.
From ConCert.Examples.Dexter2 Require Import Dexter2CPMM.
From ConCert.Examples.Dexter2 Require Import Dexter2Printers.
From ConCert.Execution Require Import ContractCommon.
Import MonadNotation.
From Coq Require Import List. Import ListNotations.
From Coq Require Import ZArith.
Require Import Extras.

Module Type Dexter2Info.
  Parameter accounts : list Address.
  Parameter gAddr : Chain -> G Address.
  Parameter cpmm_contract_addr : Address.
  Parameter token_contract_addr : Address.
  Parameter lqt_contract_addr : Address.
  Parameter token_id : N.
End Dexter2Info.

Module Dexter2Gens (Info : Dexter2Info).
  Import Info.
  Arguments SerializedValue : clear implicits.
  Arguments deserialize : clear implicits.
  Arguments serialize : clear implicits.

  Definition token_balance (addr : Address)
                           (state : FA2Token.State) : N :=
  match FMap.find token_id state.(assets) with
  | Some ledger => with_default 0%N (FMap.find addr ledger.(balances))
  | None => 0%N
  end.

  Definition liquidity_token_balance (addr : Address)
                                     (state : Dexter2FA12.State) : N :=
    with_default 0%N (AddressMap.find addr state.(Dexter2FA12.tokens)).

  (** * Dexter2 CPMM generators *)

  Definition gNonBrokeAddr (env : Environment) : G (option Address) :=
    let freq_accounts := map (fun addr => 
      (Z.to_nat ((env_account_balances env) addr), returnGenSome addr)) accounts in
    freq_ (returnGen None) freq_accounts.

  Definition gAddrWithTokens (state : FA2Token.State) : G (option Address) :=
    let freq_accounts := map (fun addr => 
      (N.to_nat (token_balance addr state), returnGenSome addr)) accounts in
    freq_ (returnGen None) freq_accounts.

  Definition gAddrWithLiquidityTokens (state : Dexter2FA12.State) : G (option Address) :=
    let freq_accounts := map (fun addr => 
      (N.to_nat (liquidity_token_balance addr state), returnGenSome addr)) accounts in
    freq_ (returnGen None) freq_accounts.


  Definition gUpdateTokenPool (env : Environment) : G (Address * Amount * Dexter2CPMM.Msg) :=
    from_addr <- gAddr env ;;
    returnGen (from_addr, 0%Z, FA2Token.other_msg UpdateTokenPool).

  Definition gXtzToToken (env : Environment) : GOpt (Address * Amount * Dexter2CPMM.Msg) :=
    from_addr <- gNonBrokeAddr env ;;
    deadline <- bindGen (choose (env.(current_slot) + 1, env.(current_slot) + 10)) returnGenSome ;;
    amount <- bindGen (choose (1%Z, (env_account_balances env) from_addr)) returnGenSome ;;
    let param := {|
      tokens_to := from_addr;
      minTokensBought := 1%N;
      xtt_deadline := deadline
    |} in
    returnGenSome (from_addr, amount, FA2Token.other_msg (XtzToToken param)).

  Definition gTokenToXtz (env : Environment) : G (Address * Amount * Dexter2CPMM.Msg) :=
    from_addr <- gAddr env ;;
    deadline <- choose (env.(current_slot) + 1, env.(current_slot) + 10) ;;
    amount <- choose (30, 50)%N ;;
    let param := {|
      xtz_to := from_addr;
      tokensSold := amount;
      minXtzBought := 1;
      ttx_deadline := deadline
    |} in
    returnGen (from_addr, 0%Z, FA2Token.other_msg (TokenToXtz param)).

  Definition gAddLiquidity (env : Environment) : GOpt (Address * Amount * Dexter2CPMM.Msg) :=
    state <- returnGen (get_contract_state Dexter2CPMM.State env cpmm_contract_addr);;
    fa2_state <- returnGen (get_contract_state FA2Token.State env token_contract_addr);;
    from_addr <- gAddrWithTokens fa2_state ;;
    deadline <- bindGen (choose (env.(current_slot) + 1, env.(current_slot) + 10)) returnGenSome ;;
    let from_token_balance := token_balance from_addr fa2_state in
    (* Amount must "match" token balance of caller. *)
    let max_amount := ((from_token_balance * state.(xtzPool)) / state.(tokenPool))%N in
    amount <- bindGen (choose (1%Z, Z.of_N max_amount)) returnGenSome ;;
    deadline <- bindGen (choose (env.(current_slot) + 1, env.(current_slot) + 10)) returnGenSome ;;
    (* For these tests [owner] is the only relevant requirement in param.*)
    let param := {|
      owner := from_addr;
      minLqtMinted := 1;
      maxTokensDeposited := 1;
      add_deadline := 1
    |} in
    returnGenSome (from_addr, amount, FA2Token.other_msg (AddLiquidity param)).
  
    Definition gRemoveLiquidity (env : Environment) : GOpt (Address * Amount * Dexter2CPMM.Msg) :=
    liquidity_state <- returnGen (get_contract_state (Dexter2FA12.State) env lqt_contract_addr);;
    from_addr <- gAddrWithLiquidityTokens liquidity_state;;
    lqt_to_burn <- bindGen (choose (1%N, liquidity_token_balance from_addr liquidity_state)) returnGenSome;;
    deadline <- bindGen (choose (env.(current_slot) + 1, env.(current_slot) + 10)) returnGenSome ;;
    let param := {|
      liquidity_to := lqt_contract_addr;
      lqtBurned := lqt_to_burn;
      minXtzWithdrawn := 1;
      minTokensWithdrawn := 1;
      remove_deadline := deadline;
    |} in
    returnGenSome (from_addr, 0%Z, FA2Token.other_msg (RemoveLiquidity param)).
    
  (** * FA2 generators *)
  Definition gBalanceOf (env : Environment) : G (Address * Amount * FA2Token.Msg) :=
    from_addr <- gAddr env ;;
    request_addr <- gAddr env ;;
    let param := {|
      bal_requests := [
        {|
          FA2LegacyInterface.owner := request_addr;
          bal_req_token_id := token_id
        |}
      ];
      bal_callback := FA2LegacyInterface.Build_callback _ None cpmm_contract_addr
    |} in
    returnGen (from_addr, 0%Z, FA2Token.msg_balance_of param).

  (** * Combined generators *)
  Definition gAction (env : Environment) : GOpt Action :=
    let call contract_addr caller_addr value msg :=
      returnGenSome (build_act caller_addr caller_addr (act_call contract_addr value msg)) in
    let call_cpmm caller_addr value msg :=
      call cpmm_contract_addr caller_addr value (@serialize Dexter2CPMM.Msg _ msg) in
    let call_token caller_addr value msg :=
      call token_contract_addr caller_addr value (@serialize FA2Token.Msg _ msg) in
    backtrack [
      (* UpdateTokenPool *)
      (1, '(caller, value, msg) <- gUpdateTokenPool env ;;
          call_cpmm caller value msg
      );
      (* XtzToToken *)
      (1, bindGenOpt (gXtzToToken env)
          (fun '(caller, value, msg) =>
            call_cpmm caller value msg
          )
      );
      (* TokenToXtz *)
      (1, '(caller, value, msg) <- gTokenToXtz env ;;
          call_cpmm caller value msg
      );
      (* AddLiquidity *)
      (1,
        '(caller, value, msg) <- gAddLiquidity env;;
        call_cpmm caller value msg
      );
      (*(* RemoveLiquidity *)
      (1,
        '(caller, value, msg) <- gRemoveLiquidity env;;
        call_cpmm caller value msg
      );*)
      (* BalanceOf *)
      (1, '(caller, value, msg) <- gBalanceOf env ;;
          call_token caller value msg
      )].

End Dexter2Gens.
