
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Examples.Ecommerce Require Import EcommerceFixed.
Import Containers.
Import MonadNotation.

From Coq Require Import ZArith.
From Coq Require Import List.
Import ListNotations.

Module Type EcommerceFixedGensInfo.
  Parameter contract_addr : Address.
  Parameter purchase_buyer : Address.
  Parameter item1_Id : nat.
  Parameter purchaseId : N.
End EcommerceFixedGensInfo.


Module EcommerceFixedGens (Info : EcommerceFixedGensInfo).
Import Info.

Definition Env := Environment.
Open Scope Z_scope.
Local Open Scope string_scope.
    
Definition gEcommerceFixedAction (env : Env): GOpt Action :=
  let call caller amount msg :=
      returnGenSome {|
          act_origin := caller;
          act_from := caller;
          act_body := act_call contract_addr amount (@serialize EcommerceFixed.Msg EcommerceFixed.Msg_serializable msg)
      |} in
  state <- returnGen (get_contract_state EcommerceFixed.State env contract_addr);;
  let buyer_balance := env.(env_account_balances) purchase_buyer in
  let itemId := item1_Id%nat in
  let cur_slot := env.(env_chain).(current_slot) in
  let buyer_dispute_delivery_commmitment := hash_bid purchaseId true 42%N in
  match FMap.find itemId state.(listings), cur_slot with
  | Some _item, 1%nat => (* This is done explicitly with cur_slot to make sure that we know the purchaseId in this generator. *)
      (* buyer_request_purchase *)
      call purchase_buyer _item.(item_value) (buyer_request_purchase itemId "notes here")
  | Some _item, _ =>
  backtrack[
    (19%nat,
      match FMap.find purchaseId state.(purchases) with
      | Some purchase => 
          match purchase.(purchase_state) with
          | requested =>
                (* buyer_abort || seller_reject_contract || seller_accept_contract *)
                backtrack [
                    (1%nat, call purchase.(buyer) 0 (buyer_abort purchaseId));
                    (1%nat, call state.(seller) 0 (seller_reject_contract purchaseId));
                    (5%nat, call state.(seller) 0 (seller_accept_contract purchaseId))
                ]
          | accepted =>
                (* buyer_call_timeout || seller_item_was_delivered *)
                backtrack [
                    (1%nat, call purchase.(buyer) 0 (buyer_call_timeout purchaseId));
                    (4%nat, call state.(seller) 0 (seller_item_was_delivered purchaseId))
                ]
          | delivered =>
                (* buyer_confirm_delivery || buyer_dispute_delivery || seller_call_timeout *)
                backtrack [
                    (1%nat, call purchase.(buyer) 0 (buyer_confirm_delivery purchaseId));
                    (1%nat, call purchase.(buyer) 0 (buyer_dispute_delivery purchaseId buyer_dispute_delivery_commmitment));
                    (4%nat, call state.(seller) 0 (seller_call_timeout purchaseId))
                ]
          | dispute =>
                random_bit <- bindGen (oneOf[returnGen true; returnGen false]) returnGenSome;;
                (* buyer_call_timeout_action || seller_forfeit_dispute || seller_counter_dispute *)
                backtrack[
                    (1%nat, call purchase.(buyer) 0 (buyer_call_timeout purchaseId));
                    (1%nat, call state.(seller) 0 (seller_forfeit_dispute purchaseId));
                    (3%nat, call state.(seller) 0 (seller_counter_dispute purchaseId random_bit))
                ]
          | counter =>
                (* buyer_open_commitment || seller_call_timeout*)
                backtrack[
                    (1%nat, call purchase.(buyer) 0 (buyer_open_commitment purchaseId true 42%N));
                    (4%nat, call state.(seller) 0 (seller_call_timeout purchaseId))

                ]
          | rejected | failed | completed => returnGen None
          end
      | _ => returnGen None
      end);
      (1% nat,
               value <- bindGen (choose (1, 5)%Z) returnGenSome ;;  
               call state.(seller) 0 (seller_update_listings itemId "updated description" value)
      )
      ]
  | _, _ => returnGen None (* Should never happen *)
  end.

End EcommerceFixedGens.