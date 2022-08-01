(*
  https://cs.au.dk/~nis/commerce/
  https://raw.githubusercontent.com/SSODelta/DecentralizedCommerce/main/Vendor.sol
*)

Require Import Blockchain.
Require Import Containers.

Require Import Serializable. 
From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import Bool.
Require Import Monads.
From Coq Require Import ZArith.
From Coq Require Import Arith.
Import ListNotations.
From ConCert.Utils Require Import RecordUpdate.
Definition required_true (b: bool) := if b then Some tt else None.
Definition required_false (b: bool) := if b then None else Some tt.

Section ECommerce.

Open Scope Z.
Context `{Base : ChainBase}.
Set Nonrecursive Elimination Schemes.

(* Simply called State in the original code *)
Inductive PurchaseState :=
  | null (* Might be unnecessary. *)
  | requested
  | accepted
  | rejected
  | delivered
  | completed
  | dispute
  | counter
  | failed.
  
Record Item :=
  build_item {
    item_value : Amount;
    item_description : string
  }.

Record Purchase :=
  build_purchase {
    commit : N; (* Should be bytes32*)
    last_block : nat; (* slot in the Chain*)
    item : nat;
    seller_bit : bool;
    notes : string;
    purchase_state : PurchaseState;
    buyer : Address;
  }.

MetaCoq Run (make_setters Purchase).

Definition listings_key_type := nat.
Definition listings_type := FMap listings_key_type Item.

Definition purchase_key_type := N.
Definition purchases_type := FMap purchase_key_type Purchase.

Record State :=
  build_state {
    seller: Address;
    listings : listings_type; (* Key is the item identifier *)
    purchases : purchases_type; (* TODO N should be somethings that corresponds to [bytes32] in Solidity!!  *)
    timeout : nat;
  }.

MetaCoq Run (make_setters State).


Record Setup :=
  build_setup {
    setup_listings : FMap nat Item;
    setup_timeout : nat
  }.

(* [id] is the key in [purchases] *)
Inductive Msg :=
| buyer_request_purchase (itemId : nat) (notes : string)
| buyer_abort (id : N) 
| buyer_confirm_delivery (id : N)
| buyer_dispute_delivery (id : N) (commitment : N)
| buyer_call_timeout (id : N)
| buyer_open_commitment (id : N) (buyer_bit : bool) (nonce : N)

| seller_call_timeout (id : N)
| seller_reject_contract (id : N)
| seller_accept_contract (id : N)
| seller_item_was_delivered (id : N)
| seller_forfeit_dispute (id : N)
| seller_counter_dispute (id : N) (random_bit : bool)
| seller_update_listings (itemId : nat) (description : string) (value : Amount)
.

Definition get_item_option itemId (listings : listings_type) := FMap.find itemId listings.
Definition get_purchase_option purchaseId (purchases : purchases_type) := FMap.find purchaseId purchases.

(*  *)
Definition TEMP_keccak256 (n1: nat) (n2 : Address) : N := 2%N.


(* In the original code, this function returns [purchaseId]. However this is not possible (or necessary) in ConCert. *)
Definition buyer_request_purchase_action (chain : Chain) (ctx : ContractCallContext) (state : State)
                                         (itemId : nat) (notes : string)
                                         : option (State * list ActionBody) :=
  let buyer := ctx_from ctx in
  let offer_money := ctx_amount ctx in
  let current_listings := listings state in
  do requested_item <- get_item_option itemId current_listings; (* If item with itemId does not exist, do nothing *)
  do required_true ((item_value requested_item) =? offer_money);
  let current_slot := current_slot chain in
  let purchaseId := TEMP_keccak256 current_slot buyer in
  let purchase :=
    {|
      commit := 0;
      last_block := current_slot;
      item := itemId;
      seller_bit := false;
      notes := notes;
      purchase_state := requested;
      buyer := buyer;
    |} in
  let updated_purchases := (FMap.add purchaseId purchase (purchases state) :  purchases_type) in
  Some (state<| purchases := updated_purchases |>, []).
  
Definition buyer_abort_action (ctx : ContractCallContext) (state : State) (purchaseId : purchase_key_type)
  : option (State * list ActionBody) :=
    let current_purchases := purchases state in
    do purchase <- get_purchase_option purchaseId current_purchases;
    do match purchase_state purchase with
       | requested => Some tt
       | _ => None
       end;
    do required_true (ctx.(ctx_from) =? purchase.(buyer))%address;
    let updated_purchase := purchase <| purchase_state := failed |> in 
    let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
    let balance := ctx_contract_balance ctx in
    Some (state <| purchases := updated_purchases|>,
          [act_transfer (purchase.(buyer)) balance]).

Definition buyer_confirm_delivery_action ctx state purchaseId
                                       : option (State * list ActionBody) :=
  let current_purchases := purchases state in
    do purchase <- get_purchase_option purchaseId current_purchases;
    do match purchase_state purchase with
       | delivered => Some tt
       | _ => None
       end;
    do required_true (ctx.(ctx_from) =? purchase.(buyer))%address;
    let updated_purchase := purchase <| purchase_state := completed |> in 
    let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
    let balance := ctx_contract_balance ctx in
    Some (state <| purchases := updated_purchases|>,
          [act_transfer (state.(seller)) balance]).

Definition buyer_dispute_delivery_action ctx state chain purchaseId commitment
          : option (State * list ActionBody) :=
  let current_purchases := purchases state in
  do purchase <- get_purchase_option purchaseId current_purchases;
  do match purchase_state purchase with
     | delivered => Some tt
     | _ => None
     end;
  do required_true (ctx.(ctx_from) =? purchase.(buyer))%address;
  let money_sent := ctx.(ctx_amount) in
  do disputed_item <- get_item_option purchase.(item) state.(listings);
  do required_true (money_sent =? disputed_item.(item_value));
  let updated_purchase := purchase <| purchase_state := dispute |>
                                   <| commit := commitment |>
                                   <| last_block := current_slot chain |> in 
  let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
  Some (state <| purchases := updated_purchases|>, []).

Definition buyer_call_timeout_action ctx state chain purchaseId
  : option (State * list ActionBody) :=
  let current_purchases := purchases state in
  do purchase <- get_purchase_option purchaseId current_purchases;
  do match purchase_state purchase with
     | dispute | accepted => Some tt
     | _ => None
     end;
  do required_true (ctx.(ctx_from) =? purchase.(buyer))%address;
  do required_true (purchase.(last_block) + state.(timeout) <? chain.(current_slot))%nat;
  let updated_purchase := purchase <| purchase_state := failed |> in 
  let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
  let balance := ctx_contract_balance ctx in
  Some (state <| purchases := updated_purchases|>,
        [act_transfer (purchase.(buyer)) balance]).


(* TEMP HASH FUNCTION - Not cryptographically secure at all! *)
Definition hash_bid (id : N) (buyer_bit : bool) (nonce : N) : N :=
    Npos (countable.encode (id, buyer_bit, nonce)).
Arguments hash_bid : simpl never.
        (* TODO !!*)
Print get_item_option.
Definition buyer_open_commitment_action ctx state purchaseId buyer_bit nonce
  : option (State * list ActionBody) :=
  let current_purchases := state.(purchases) in
  do purchase <- get_purchase_option purchaseId current_purchases;
  do required_true (ctx.(ctx_from) =? purchase.(buyer))%address;
  do match purchase_state purchase with
     | counter => Some tt
     | _ => None
     end;
  do required_true ((hash_bid purchaseId buyer_bit nonce =? purchase.(commit))%N); (* TMP TODO!! Use hashing! *)
  let updated_purchase := purchase <| purchase_state := failed |> in
  let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
  let target_transaction := if (eqb purchase.(seller_bit) buyer_bit) then state.(seller) else purchase.(buyer) in
  do item <- get_item_option purchase.(item) state.(listings);
  Some (state <| purchases := updated_purchases |>,
        [act_transfer target_transaction item.(item_value)]).

Definition seller_call_timeout_action ctx state chain purchaseId
  : option (State * list ActionBody) :=
  let current_purchases := purchases state in
  do purchase <- get_purchase_option purchaseId current_purchases;
  do match purchase_state purchase with
     | delivered | counter => Some tt
     | _ => None
     end;
  do required_true (ctx.(ctx_from) =? state.(seller))%address;
  do required_true (purchase.(last_block) + state.(timeout) <? chain.(current_slot))%nat;
  let updated_purchase := purchase <| purchase_state := completed |> in 
  let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
  let balance := ctx_contract_balance ctx in
  Some (state <| purchases := updated_purchases|>,
        [act_transfer (state.(seller)) balance]).

Definition seller_reject_contract_action ctx state purchaseId
  : option (State * list ActionBody) :=
  let current_purchases := purchases state in
  do purchase <- get_purchase_option purchaseId current_purchases;
  do match purchase_state purchase with
     | requested => Some tt
     | _ => None
     end;
  do required_true (ctx.(ctx_from) =? state.(seller))%address;
  let updated_purchase := purchase <| purchase_state := rejected |> in 
  let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
  let balance := ctx_contract_balance ctx in
  Some (state <| purchases := updated_purchases|>,
        [act_transfer (purchase.(buyer)) balance]).

Definition seller_accept_contract_action ctx state chain purchaseId
  : option (State * list ActionBody) :=
  let current_purchases := purchases state in
  do purchase <- get_purchase_option purchaseId current_purchases;
  do match purchase_state purchase with
     | requested => Some tt
     | _ => None
     end;
  do required_true (ctx.(ctx_from) =? state.(seller))%address;
  let updated_purchase := purchase <| purchase_state := accepted |>
                                   <| last_block := chain.(current_slot) |> in 
  let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
  Some (state <| purchases := updated_purchases|>, []).

Definition seller_item_was_delivered_action ctx state chain purchaseId
  : option (State * list ActionBody) :=
  let current_purchases := purchases state in
  do purchase <- get_purchase_option purchaseId current_purchases;
  do match purchase_state purchase with
     | accepted => Some tt
     | _ => None
     end;
  do required_true (ctx.(ctx_from) =? state.(seller))%address;
  let updated_purchase := purchase <| purchase_state := delivered |>
                                   <| last_block := chain.(current_slot) |> in 
  let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
  Some (state <| purchases := updated_purchases|>, []).

Definition seller_forfeit_dispute_action ctx state purchaseId
  : option (State * list ActionBody) :=
  let current_purchases := purchases state in
  do purchase <- get_purchase_option purchaseId current_purchases;
  do match purchase_state purchase with
     | dispute => Some tt
     | _ => None
     end;
  do required_true (ctx.(ctx_from) =? state.(seller))%address;
  let updated_purchase := purchase <| purchase_state := failed |> in 
  let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
  let balance := ctx_contract_balance ctx in
  Some (state <| purchases := updated_purchases|>,
        [act_transfer (purchase.(buyer)) balance]).

Definition seller_counter_dispute_action ctx state chain purchaseId random_bit
  : option (State * list ActionBody) :=
  let current_purchases := purchases state in
  do purchase <- get_purchase_option purchaseId current_purchases;
  do match purchase_state purchase with
     | dispute => Some tt
     | _ => None
     end;
  do required_true (ctx.(ctx_from) =? state.(seller))%address;
  let money_sent := ctx.(ctx_amount) in
  do disputed_item <- get_item_option purchase.(item) state.(listings);
  do required_true (money_sent =? disputed_item.(item_value));
  let updated_purchase := purchase <| purchase_state := counter |>
                                   <| last_block := chain.(current_slot) |>
                                   <| seller_bit := random_bit |> in 
  let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
  Some (state <| purchases := updated_purchases|>, []).

Definition seller_update_listings_action ctx state itemId descr value
  : option (State * list ActionBody) :=
  do required_true (ctx.(ctx_from) =? state.(seller))%address;
  let current_listings := state.(listings) in
  let new_item := {| item_value :=  value; item_description := descr |} in 
  let updated_listings := FMap.add itemId new_item current_listings in
  Some (state <| listings := updated_listings |>, []).

  
Definition receive (chain : Chain) (ctx : ContractCallContext)
                   (state : State) (msg : option Msg)
                   : option (State * list ActionBody) :=
  match msg with
  | Some msg_content =>
      match msg_content with
      | buyer_request_purchase itemId notes => buyer_request_purchase_action chain ctx state itemId notes
      | buyer_abort id => buyer_abort_action ctx state id
      | buyer_confirm_delivery id => buyer_confirm_delivery_action ctx state id
      | buyer_dispute_delivery id commitment => buyer_dispute_delivery_action ctx state chain id commitment
      | buyer_call_timeout id => buyer_call_timeout_action ctx state chain id
      | buyer_open_commitment id buyer_bit nonce => buyer_open_commitment_action ctx state id buyer_bit nonce
      | seller_call_timeout id => seller_call_timeout_action ctx state chain id
      | seller_reject_contract id => seller_reject_contract_action ctx state id
      | seller_accept_contract id => seller_accept_contract_action ctx state chain id
      | seller_item_was_delivered id => seller_item_was_delivered_action ctx state chain id
      | seller_forfeit_dispute id => seller_forfeit_dispute_action ctx state id
      | seller_counter_dispute id random_bit => seller_counter_dispute_action ctx state chain id random_bit
      | seller_update_listings itemId description value => seller_update_listings_action ctx state itemId description value
      end
  | _ => None
  end.

Definition init (chain : Chain) (ctx : ContractCallContext) (setup : Setup)
  : option State :=
  let seller := ctx_from ctx in
  let listings := setup_listings setup in
  let timeout := setup_timeout setup in
  do required_true (timeout <? 0)%nat;
  Some {|
    seller := seller;
    listings := listings;
    purchases := FMap.empty;
    timeout := timeout;
  |}.

Global Instance Item_serializable : Serializable Item :=
  Derive Serializable Item_rect<build_item>.
  
  
Global Instance PurchaseState_serializable : Serializable PurchaseState :=
  Derive Serializable PurchaseState_rect<null, requested, accepted, rejected, delivered, completed, dispute, counter, failed>.
  
Global Instance Purchase_serializable : Serializable Purchase :=
  Derive Serializable Purchase_rect<build_purchase>.

Global Instance Setup_serializable : Serializable Setup :=
  Derive Serializable Setup_rect<build_setup>.

  
Global Instance Msg_serializable : Serializable Msg :=
  Derive Serializable Msg_rect<buyer_request_purchase,
                               buyer_abort,
                               buyer_confirm_delivery,
                               buyer_dispute_delivery,
                               buyer_call_timeout,
                               buyer_open_commitment,
                               seller_call_timeout,
                               seller_reject_contract,
                               seller_accept_contract,
                               seller_item_was_delivered,
                               seller_forfeit_dispute,
                               seller_counter_dispute,
                               seller_update_listings
                              >.


Global Instance State_serializable : Serializable State :=
  Derive Serializable State_rect<build_state>. 

Definition contract : Contract Setup Msg State := 
    build_contract init receive.
End ECommerce.