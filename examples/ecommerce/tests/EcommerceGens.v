
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Examples.Ecommerce Require Import Ecommerce.
Import Containers.
Import MonadNotation.

From Coq Require Import ZArith.
From Coq Require Import List.

Module Type EcommerceGensInfo.
  Parameter contract_addr : Address.
  Parameter purchase_buyer : Address.
End EcommerceGensInfo.


Module EcommerceGens (Info : EcommerceGensInfo).
Import Info.

Definition Env := Environment.
Open Scope Z_scope.
Local Open Scope string_scope.


Definition gEcommerceAction (env : Env): GOpt Action :=
  let call caller amount msg :=
      returnGenSome {|
          act_origin := caller;
          act_from := caller;
          act_body := act_call contract_addr amount (@serialize Ecommerce.Msg Ecommerce.Msg_serializable msg)
      |} in
  state <- returnGen (get_contract_state Ecommerce.State env contract_addr);;
  let buyer_balance := env.(env_account_balances) purchase_buyer in
  let itemId := 42%nat in
  let cur_slot := env.(env_chain).(current_slot) in
  let purchaseId := hash_bid2 2%nat purchase_buyer in (* This is the purchaseId *)

  match FMap.find itemId state.(listings), cur_slot with
  | Some _item, 2%nat => (* This is done explicitly to make sure that we know the purchaseId in this generator *)
      (* buyer_request_purchase *)
      if buyer_balance <? _item.(item_value) 
      then returnGen None
      else
      call state.(seller) _item.(item_value) (buyer_request_purchase itemId "notes here")
  | Some _item, _ =>
      returnGen None
  | _, _ =>
      (* seller_update_listings *)
      value <- bindGen (choose (1, 7)%Z) returnGenSome ;;
      call state.(seller) 0 (seller_update_listings 42 "description here" value)
  end.

End EcommerceGens.