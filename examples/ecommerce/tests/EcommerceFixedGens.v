
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
  Parameter buyers : list Address.
  Parameter item_ids : list nat.
End EcommerceFixedGensInfo.


Module EcommerceFixedGens (Info : EcommerceFixedGensInfo).
Import Info.

Definition Env := Environment.
Open Scope Z_scope.
Local Open Scope string_scope.
    
Definition constant_buyer_bit := true.
Definition constant_buyer_nonce := 42%N.

Definition is_active_purchase (key_purchase : (N * Purchase)) :=
    let '(key, purchase) := key_purchase in
    match purchase.(purchase_state) with
    | completed | rejected | failed => false
    | _ => true
    end.

Definition active_item_ids (state : State) :=
    map fst (FMap.elements state.(listings)).

(* Gets active buyer and a corresponding purchaseId *)
Definition gActivePurchase (state : State) : GOpt (N * Purchase) :=
    let actives_purchases := filter is_active_purchase (FMap.elements state.(purchases)) in
    let address_purchaseId_purchases := map (fun '(key, purchase) => returnGenSome (key, purchase)) actives_purchases in
    oneOf_ (returnGen None) address_purchaseId_purchases.

Definition gOptRequestPurchase (state : State) : GOpt (Address * Amount * Msg) :=
    buyer <- oneOf_ (returnGen None) (map returnGenSome buyers);;
    itemId <- oneOf_ (returnGen None) (map returnGenSome (active_item_ids state));;
    item <- returnGen (FMap.find itemId state.(listings));;
    returnGenSome (buyer, item.(item_value), (buyer_request_purchase itemId "notes here")).

Definition gOptUpdateListings (state : State) : GOpt (Address * Amount * Msg) :=
    itemId <- bindGenOpt (oneOf_ (returnGen None) (map returnGenSome item_ids)) returnGenSome;;
    value <- bindGen (choose (1,4)) returnGenSome;;
    returnGenSome (state.(seller), 0, seller_update_listings itemId "updated description" value).
    
Definition gEcommerceFixedAction (env : Env): GOpt Action :=
  let call caller amount msg :=
      returnGenSome {|
          act_origin := caller;
          act_from := caller;
          act_body := act_call contract_addr amount (@serialize EcommerceFixed.Msg EcommerceFixed.Msg_serializable msg)
      |} in
  state <- returnGen (get_contract_state EcommerceFixed.State env contract_addr);;
  backtrack[
    (* buyer_request_purchase *)
    (4%nat, '(caller, amount, msg) <- gOptRequestPurchase state;;
            call caller amount msg    
    );
    (* update_listings *)
    (1%nat, '(caller, amount, msg) <- gOptUpdateListings state;;
            call caller amount msg    
    );
    (** Purchase interactions **)
    (15%nat,
     '(purchaseId, purchase) <- gActivePurchase state;;
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
                (1%nat, let buyer_dispute_delivery_commmitment := hash_bid purchaseId constant_buyer_bit constant_buyer_nonce in
                        item <- returnGen (FMap.find 2%nat(*purchase.(itemId)*) state.(listings));;
                        call purchase.(buyer) item.(item_value) (buyer_dispute_delivery purchaseId buyer_dispute_delivery_commmitment));
                (1%nat, call state.(seller) 0 (seller_call_timeout purchaseId))
            ]
        | dispute =>
            (* buyer_call_timeout_action || seller_forfeit_dispute || seller_counter_dispute *)
            backtrack[
                (1%nat, call purchase.(buyer) 0 (buyer_call_timeout purchaseId));
                (1%nat, call state.(seller) 0 (seller_forfeit_dispute purchaseId));
                (3%nat, item <- returnGen (FMap.find purchase.(itemId) state.(listings));;
                        random_bit <- bindGen (oneOf[returnGen true; returnGen false]) returnGenSome;;
                        call state.(seller) item.(item_value) (seller_counter_dispute purchaseId random_bit))
            ]
        | counter =>
            (* buyer_open_commitment || seller_call_timeout*)
            backtrack[
                (4%nat, call purchase.(buyer) 0 (buyer_open_commitment purchaseId constant_buyer_bit constant_buyer_nonce));
                (1%nat, call state.(seller) 0 (seller_call_timeout purchaseId))

            ]
        | rejected | failed | completed  => returnGen None (* should never happen! *)
    end
    )
  ].
  
(*

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
                    (1%nat, call purchase.(buyer) _item.(item_value) (buyer_dispute_delivery purchaseId buyer_dispute_delivery_commmitment));
                    (4%nat, call state.(seller) 0 (seller_call_timeout purchaseId))
                ]
          | dispute =>
                random_bit <- bindGen (oneOf[returnGen true; returnGen false]) returnGenSome;;
                (* buyer_call_timeout_action || seller_forfeit_dispute || seller_counter_dispute *)
                backtrack[
                    (1%nat, call purchase.(buyer) 0 (buyer_call_timeout purchaseId));
                    (1%nat, call state.(seller) 0 (seller_forfeit_dispute purchaseId));
                    (3%nat, call state.(seller) _item.(item_value) (seller_counter_dispute purchaseId random_bit))
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
*)
End EcommerceFixedGens.