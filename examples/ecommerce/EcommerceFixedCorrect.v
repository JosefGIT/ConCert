From ConCert.Examples.Ecommerce Require Import EcommerceFixed.
From ConCert.Execution Require Import BuildUtils.
From ConCert.Utils Require Import Automation.
From Coq Require Import ZArith.

From ConCert.Execution Require Import Serializable.
Require Import Blockchain.
Require Import Containers.
Require Import Extras.
From ConCert.Utils Require Import RecordUpdate.
From Coq Require Import Bool.
From Coq Require Import Lia.
From Coq Require Import List.
Import ListNotations.

Section Theories.

Context `{Base : ChainBase}. 

Arguments hash_bid : simpl never.
Arguments hash_purchaseId : simpl never.


Ltac destruct_message :=
  match goal with
  | receive_some : context[receive _ _ _ _ ?msg = Some (_, _)] |- _ => destruct msg as [?m|]; try discriminate; destruct m
  (* At the moment receive with "EcommerceFixed" prefix is also necessary *)
  | receive_some : context[EcommerceFixed.receive _ _ _ ?msg = Some (_, _)] |- _ => destruct msg as [?m|]; try discriminate; destruct m
  end.


Ltac receive_simpl_step g :=
  match type of g with
  | context[find_purchase] => unfold find_purchase in g; cbn in g
  | context[find_item] => unfold find_item in g; cbn in g
  | context[purchase_exists] => unfold purchase_exists in g; cbn in g
  | context[FMap.find _ ?v] => destruct (FMap.find _ v) eqn:?; cbn in g
  | context[required_true ?cond] => destruct cond eqn:?E; inversion E; cbn in g
  | context[required_false ?cond] => destruct cond eqn:?E; inversion E; cbn in g

  | context[setter_from_getter_State_purchases] => unfold setter_from_getter_State_purchases in g; cbn in g
  | context[set_State_purchases] => unfold set_State_purchases in g; cbn in g
  | context[setter_from_getter_Purchase_last_block] => unfold setter_from_getter_Purchase_last_block in g; cbn in g
  | context[set_Purchase_last_block] => unfold set_Purchase_last_block in g; cbn in g
  | context[setter_from_getter_Purchase_purchase_state] => unfold setter_from_getter_Purchase_purchase_state in g; cbn in g
  | context[set_Purchase_purchase_state] => unfold set_Purchase_purchase_state in g; cbn in g
  | context[setter_from_getter_Purchase_seller_bit] => unfold setter_from_getter_Purchase_seller_bit in g; cbn in g
  | context[set_Purchase_seller_bit] => unfold set_Purchase_seller_bit in g; cbn in g
  | context[setter_from_getter_State_listings] => unfold setter_from_getter_State_listings in g; cbn in g
  | context[set_State_listings] => unfold set_State_listings in g; cbn in g
  end. 

Tactic Notation "receive_simpl" constr(g) := cbn in g; repeat (receive_simpl_step g); try discriminate.

Ltac receive_simpl_goal_step :=
  match goal with
  | |- context[find_purchase] => unfold find_purchase
  | |- context[find_item] => unfold find_item
  | |- context[purchase_exists] => unfold purchase_exists
  | |- context[purchase_state_eq] => unfold purchase_state_eq

  | |- context[setter_from_getter_State_purchases] => unfold setter_from_getter_State_purchases
  | |- context[set_State_purchases] => unfold set_State_purchases
  | |- context[setter_from_getter_Purchase_last_block] => unfold setter_from_getter_Purchase_last_block
  | |- context[set_Purchase_last_block] => unfold set_Purchase_last_block
  | |- context[setter_from_getter_Purchase_purchase_state] => unfold setter_from_getter_Purchase_purchase_state
  | |- context[set_Purchase_purchase_state] => unfold set_Purchase_purchase_state
  | |- context[setter_from_getter_Purchase_seller_bit] => unfold setter_from_getter_Purchase_seller_bit
  | |- context[set_Purchase_seller_bit] => unfold set_Purchase_seller_bit
  | |- context[setter_from_getter_State_listings] => unfold setter_from_getter_State_listings
  | |- context[set_State_listings] => unfold set_State_listings
  end. 

Tactic Notation "receive_simpl_goal" := cbn; repeat (receive_simpl_goal_step; cbn).

Open Scope Z.
  
Lemma purchase_state_eq_correct : forall (state1 state2 : PurchaseState),
  state1 = state2 <-> purchase_state_eq state1 state2 = true.
Proof.
  intros *. split; intros; destruct state1; destruct state2; try discriminate; reflexivity.
Qed.

(**** Correctness for messages *****)
Lemma buyer_request_purchase_correct : forall chain ctx prev_state new_state new_acts _itemId _notes,
  EcommerceFixed.receive chain ctx prev_state (Some (buyer_request_purchase _itemId _notes)) = Some (new_state, new_acts)
  <->
     (exists item,
         FMap.find _itemId prev_state.(listings) = Some item
      /\ FMap.find _itemId new_state.(listings) = Some item
      /\ item.(item_value) = ctx.(ctx_amount))
  /\ (exists purchaseId new_purchase,
         purchaseId = hash_purchaseId chain.(current_slot) (ctx.(ctx_from))
      /\ FMap.find purchaseId prev_state.(purchases) = None
      /\ new_state.(purchases) = FMap.add purchaseId new_purchase prev_state.(purchases)
      /\ new_purchase.(itemId) = _itemId
      /\ new_purchase.(last_block) = chain.(current_slot)
      /\ new_purchase.(purchase_state) = requested
      /\ new_purchase.(buyer) = ctx.(ctx_from)
      /\ new_purchase.(seller_bit) = false
      /\ new_purchase.(commit) = 0%N
      /\ new_purchase.(notes) = _notes)
  /\ prev_state.(listings) = new_state.(listings)
  /\ prev_state.(seller) = new_state.(seller)
  /\ prev_state.(timeout) = new_state.(timeout)
  /\ new_acts = []
  .
Proof.
  intros * . split.
  - intros receive_some.
    receive_simpl receive_some.
    remember ({|
    commit := 0;
    last_block := current_slot
      chain;
    itemId := _itemId;
    seller_bit := false;
    notes := _notes;
    purchase_state := requested;
    buyer := ctx_from ctx |})
    as new_purchase.
    repeat split; try now inversion receive_some.
    + exists i. repeat split; try now inversion receive_some.
      now apply Z.eqb_eq in E.
    + remember (hash_purchaseId chain.(current_slot) ctx.(ctx_from)) as new_purchaseId.
      exists new_purchaseId, new_purchase.
      repeat split; try now inversion Heqnew_purchase.
      now inversion receive_some.
  - intros ([item (prev_item & new_item & amount_sent)] &
            (purchaseId & new_purchase & purchaseId_hash & not_found_purchase & purchase_added & purchase_itemId & purchase_last_block &
             ppurchase_state & purchase_buyer & purchase_seller_bit & purchase_commit & purchase_notes) &
             const_listings & const_seller & const_timeout & empty_acts).
    receive_simpl_goal.
    setoid_rewrite prev_item.
    apply Z.eqb_eq in amount_sent. rewrite amount_sent; cbn.
    rewrite <- purchaseId_hash.
    setoid_rewrite not_found_purchase; cbn.
    rewrite empty_acts.
    rewrite const_listings, const_seller, const_timeout.
    rewrite <- purchase_last_block, <- purchase_commit, <- purchase_itemId, <- purchase_seller_bit,
            <- purchase_notes, <- ppurchase_state, <- purchase_buyer.   
    destruct new_purchase; destruct new_state; cbn in *.
    now setoid_rewrite <- purchase_added. 
Qed.

Lemma seller_accept_contract_correct : forall chain ctx prev_state new_state new_acts id,
  EcommerceFixed.receive chain ctx prev_state (Some (seller_accept_contract id)) = Some (new_state, new_acts)
  <->
     (exists purchase updated_purchase,
        FMap.find id prev_state.(purchases) = Some purchase
      /\ purchase.(purchase_state) = requested
      /\ FMap.find id new_state.(purchases) = Some updated_purchase
      /\ updated_purchase.(purchase_state) = accepted
      /\ updated_purchase.(last_block) = chain.(current_slot)
      /\ updated_purchase.(commit) = purchase.(commit)
      /\ updated_purchase.(itemId) = purchase.(itemId)
      /\ updated_purchase.(seller_bit) = purchase.(seller_bit)
      /\ updated_purchase.(notes) = purchase.(notes)
      /\ updated_purchase.(buyer) = purchase.(buyer)
      /\ new_state.(purchases) = FMap.add id updated_purchase prev_state.(purchases))
  /\ (ctx.(ctx_from) =? prev_state.(seller) = true)%address
  /\ prev_state.(listings) = new_state.(listings)
  /\ prev_state.(seller) = new_state.(seller)
  /\ prev_state.(timeout) = new_state.(timeout)
  /\ new_acts = [].
Proof.
  intros *. split.
  - intros receive_some. cbn in *.
    receive_simpl receive_some.
    remember ({|
      commit := commit p;
      last_block := current_slot chain;
      itemId := itemId p;
      seller_bit := seller_bit p;
      notes := notes p;
      purchase_state := accepted;
      buyer := buyer p |})
    as updated_purchase.
    inversion receive_some; clear receive_some. cbn. repeat split.
    exists p, updated_purchase. repeat split; try now inversion Hequpdated_purchase.
    + now apply purchase_state_eq_correct in E.
    + apply FMap.find_add.
  - intros ([purchase [updated_purchase (purchase_found & state_requested & updated_purchase_found &
                updated_state_accepted & block_current & commit_constant & item_constant &
                seller_bit_constant & notes_constant & buyer_constant & purchase_added)]] &
             ctx_from_seller & listings_constant & seller_constant & timeout_constant & no_acts).
    receive_simpl_goal.
    setoid_rewrite purchase_found.
    rewrite state_requested; cbn.
    rewrite ctx_from_seller; cbn.
    rewrite no_acts; cbn.
    rewrite seller_constant, listings_constant, timeout_constant.
    rewrite <- updated_state_accepted, <- block_current, <- commit_constant, <- item_constant,
            <- seller_bit_constant, <- notes_constant, <- buyer_constant.
            auto.
    destruct updated_purchase; destruct new_state; cbn in *.
    now setoid_rewrite <- purchase_added.
Qed.

Lemma buyer_dispute_delivery_correct : forall chain ctx prev_state new_state new_acts id commitment,
  EcommerceFixed.receive chain ctx prev_state (Some (buyer_dispute_delivery id commitment)) = Some (new_state, new_acts)
  <->
  (exists purchase updated_purchase item,
     FMap.find id prev_state.(purchases) = Some purchase
  /\ (ctx.(ctx_from) =? purchase.(buyer))%address = true
  /\ purchase.(purchase_state) = delivered
  /\ FMap.find purchase.(itemId) prev_state.(listings) = Some item
  /\ (ctx.(ctx_amount) =? item.(item_value)) = true
  /\ updated_purchase.(purchase_state) = dispute
  /\ updated_purchase.(last_block) = chain.(current_slot)
  /\ new_state.(purchases) = FMap.add id updated_purchase prev_state.(purchases)
  (* These fields should stay constant *)
  /\ commitment = updated_purchase.(commit)
  /\ purchase.(itemId) = updated_purchase.(itemId)
  /\ purchase.(seller_bit) = updated_purchase.(seller_bit)
  /\ purchase.(notes) = updated_purchase.(notes)
  /\ purchase.(buyer) = updated_purchase.(buyer))
  /\ prev_state.(listings) = new_state.(listings)
  /\ prev_state.(seller) = new_state.(seller)
  /\ prev_state.(timeout) = new_state.(timeout)
  
  /\ new_acts = []
  .
Proof.
  intros *. split.
  - intros receive_some.
    receive_simpl receive_some.
    remember ({|
    commit := commitment;
    last_block := current_slot chain;
    itemId := itemId p;
    seller_bit := seller_bit p;
    notes := notes p;
    purchase_state := dispute;
    buyer := buyer p |})
    as updated_purchase.
    repeat split; try now inversion receive_some.
    exists p, updated_purchase, i.
    repeat split; try now inversion Hequpdated_purchase.
    + now apply purchase_state_eq_correct in E.
    + now inversion receive_some.
  - intros ([purchase [updated_purchase [item 
            (purchase_found & purchase_from & state_delivered & item_found & item_val & upd_purchase_from & block_current & upd_purchases & com & const_item & const_seller_bit & const_notes & const_buyer)
  ]]] & const_listings & const_seller & const_timeout & acts_empty).
  receive_simpl_goal.
  setoid_rewrite purchase_found.
  rewrite state_delivered, purchase_from; cbn.
  setoid_rewrite item_found.
  rewrite item_val; cbn.
  rewrite acts_empty.

  rewrite const_item, const_seller_bit, const_notes, const_buyer,
          const_listings, const_seller, const_timeout,
          com, <- upd_purchase_from, <- block_current.
  destruct updated_purchase; destruct new_state;
  now setoid_rewrite <- upd_purchases.
Qed.

Lemma buyer_open_commitment_correct : forall chain ctx prev_state new_state new_acts id buyer_bit nonce,
  EcommerceFixed.receive chain ctx prev_state (Some (buyer_open_commitment id buyer_bit nonce)) = Some (new_state, new_acts)
  <->
  (exists purchase updated_purchase _item,
     FMap.find id prev_state.(purchases) = Some purchase
  /\ FMap.find id new_state.(purchases) = Some updated_purchase
  /\ FMap.find purchase.(itemId) prev_state.(listings) = Some _item
  /\ new_state.(purchases) = FMap.add id updated_purchase prev_state.(purchases)
  (* Only state should change in the targeted purchase *)
  /\ failed = updated_purchase.(purchase_state)
  /\ purchase.(last_block) = updated_purchase.(last_block)
  /\ purchase.(commit) = updated_purchase.(commit)
  /\ purchase.(itemId) = updated_purchase.(itemId)
  /\ purchase.(seller_bit) = updated_purchase.(seller_bit)
  /\ purchase.(notes) = updated_purchase.(notes)
  /\ purchase.(buyer) = updated_purchase.(buyer)
  
  /\ purchase.(purchase_state) = counter
  /\ hash_bid id buyer_bit nonce = purchase.(commit)
  /\ (ctx.(ctx_from) =? purchase.(buyer))%address = true
  /\ (eqb purchase.(seller_bit) buyer_bit = true
     -> new_acts = [act_transfer purchase.(buyer) (2*_item.(item_value))])
  /\ (eqb purchase.(seller_bit) buyer_bit = false
     -> new_acts = [act_transfer prev_state.(seller) (2*_item.(item_value))])
  )
  /\ prev_state.(listings) = new_state.(listings)
  /\ prev_state.(seller) = new_state.(seller)
  /\ prev_state.(timeout) = new_state.(timeout)
  .
  intros *. split.
  - intros receive_some.
    receive_simpl receive_some.
    remember ({|
    commit := commit p;
    last_block := last_block p;
    itemId := itemId p;
    seller_bit := seller_bit p;
    notes := notes p;
    purchase_state := failed;
    buyer := buyer p |})
    as updated_purchase.
    repeat split; try now inversion Hequpdated_purchase; try now inversion receive_some.
    exists p, updated_purchase, i.
    repeat split; try now inversion Hequpdated_purchase.
    + inversion receive_some; cbn. apply FMap.find_add.
    + now inversion receive_some.
    + now apply purchase_state_eq_correct in E0.
    + now apply N.eqb_eq in E1.
    + intros eq_bits. inversion receive_some. rewrite eq_bits. now rewrite H0.
    + intros neq_bits. inversion receive_some. now rewrite neq_bits. 
  - intros ([purchase [updated_purchase [_item
            (purchase_found & updated_purchase_found & item_found & purchases_updated & upd_purchase_failed &
             const_block & const_commit & const_item & const_seller_bit & const_notes & const_buyer &
             purchase_counter & correct_hash & ctx_from_buyer & eq_bits & neq_bits)]]] &
             const_listings & const_seller & const_timeout).
    receive_simpl_goal.
    setoid_rewrite purchase_found.
    rewrite ctx_from_buyer; cbn.
    rewrite purchase_counter; cbn.
    apply N.eqb_eq in correct_hash; rewrite correct_hash; cbn.
    setoid_rewrite item_found.
    rewrite const_seller, const_listings, const_timeout.
    rewrite const_commit, const_block, const_item,
            const_seller_bit,const_notes, const_buyer.
    rewrite upd_purchase_failed.
    destruct updated_purchase; destruct new_state; cbn in *. auto.
    setoid_rewrite <- purchases_updated.  
    rewrite const_seller_bit in eq_bits, neq_bits.
    destruct (eqb seller_bit buyer_bit) eqn:E.
    + rewrite eq_bits; easy.
    + rewrite neq_bits; easy.
Qed.

Lemma seller_item_was_delivered_correct : forall chain ctx prev_state new_state new_acts id,
  EcommerceFixed.receive chain ctx prev_state (Some (seller_item_was_delivered id)) = Some (new_state, new_acts)
  <->
  (exists purchase updated_purchase,
      FMap.find id prev_state.(purchases) = Some purchase
   /\ FMap.find id new_state.(purchases) = Some updated_purchase
   /\ new_state.(purchases) = FMap.add id updated_purchase prev_state.(purchases)
   /\ purchase.(purchase_state) = accepted
   /\ updated_purchase.(purchase_state) = delivered
   /\ updated_purchase.(last_block) = chain.(current_slot)
   (* These should remain constant *)
   /\ purchase.(commit) = updated_purchase.(commit)
   /\ purchase.(itemId) = updated_purchase.(itemId)
   /\ purchase.(seller_bit) = updated_purchase.(seller_bit)
   /\ purchase.(notes) = updated_purchase.(notes)
   /\ purchase.(buyer) = updated_purchase.(buyer))
  /\ prev_state.(listings) = new_state.(listings)
  /\ prev_state.(seller) = new_state.(seller)
  /\ prev_state.(timeout) = new_state.(timeout)

  /\ (ctx.(ctx_from) =? prev_state.(seller))%address = true
  /\ new_acts = []
  .
Proof.
  intros *. split.
  - intros receive_some.
    receive_simpl receive_some.
    repeat split; try now inversion receive_some.
    remember ({|
    commit := commit p;
    last_block := current_slot chain;
    itemId := itemId p;
    seller_bit := seller_bit p;
    notes := notes p;
    purchase_state := delivered;
    buyer := buyer p |})
    as updated_purchase.
    exists p, updated_purchase.
    repeat split; try now inversion Hequpdated_purchase; try now inversion receive_some.
    + inversion receive_some; cbn. apply FMap.find_add.
    + now inversion receive_some.
    + now apply purchase_state_eq_correct in E.
  - intros ([purchase [updated_purchase
            (found_purchase & found_upd_purchase & purchases_updated & purchase_accepted & upd_purchase_delivered & upd_purchase_block &
             const_commit & const_item & const_seller_bit & const_notes & const_buyer)]] &
            const_listings & const_seller & const_timeout & from_seller & empty_acts).
    receive_simpl_goal.
    setoid_rewrite found_purchase.
    rewrite purchase_accepted, from_seller; cbn.
    rewrite const_seller, const_listings, const_timeout.
    rewrite const_commit, const_item, const_notes, const_seller_bit, const_buyer.
    rewrite <- upd_purchase_delivered, <- upd_purchase_block, empty_acts.
    destruct updated_purchase; destruct new_state; cbn.
    now setoid_rewrite purchases_updated.
Qed.

Lemma seller_counter_dispute_correct : forall chain ctx prev_state new_state new_acts id random_bit,
  EcommerceFixed.receive chain ctx prev_state (Some (seller_counter_dispute id random_bit)) = Some (new_state, new_acts)
  <->
  (exists purchase updated_purchase item,
      FMap.find id prev_state.(purchases) = Some purchase
   /\ FMap.find id new_state.(purchases) = Some updated_purchase
   /\ FMap.find purchase.(itemId) prev_state.(listings) = Some item
   /\ new_state.(purchases) = FMap.add id updated_purchase prev_state.(purchases)
   /\ purchase.(purchase_state) = dispute
   /\ updated_purchase.(seller_bit) = random_bit
   /\ updated_purchase.(purchase_state) = counter
   /\ updated_purchase.(last_block) = chain.(current_slot)
   /\ ctx.(ctx_amount) = item.(item_value)
   (* These should remain constant *)
   /\ purchase.(commit) = updated_purchase.(commit)
   /\ purchase.(itemId) = updated_purchase.(itemId)
   /\ purchase.(notes) = updated_purchase.(notes)
   /\ purchase.(buyer) = updated_purchase.(buyer))
  /\ prev_state.(listings) = new_state.(listings)
  /\ prev_state.(seller) = new_state.(seller)
  /\ prev_state.(timeout) = new_state.(timeout)

  /\ (ctx.(ctx_from) =? prev_state.(seller))%address = true
  /\ new_acts = []
.
Proof.
  intros *. split.
  - intros receive_some.
    receive_simpl receive_some.
    repeat split; try now inversion receive_some.
    unfold setter_from_getter_Purchase_seller_bit in *.
    unfold set_Purchase_seller_bit in *.
    remember ({|
    commit := commit p;
    last_block := current_slot chain;
    itemId := itemId p;
    seller_bit := random_bit;
    notes := notes p;
    purchase_state := counter;
    buyer := buyer p |})
    as updated_purchase.
    exists p, updated_purchase, i.
    repeat split; try now inversion Hequpdated_purchase.
    + inversion receive_some; cbn. apply FMap.find_add.
    + now inversion receive_some.
    + now apply purchase_state_eq_correct in E.
    + now apply Z.eqb_eq in E1.
  - intros ([purchase [updated_purchase [item (
             found_purchase & found_upd_purchase & found_item & updated_purchases & purchase_dispute &
             seller_bit_rand & upd_purchase_counter & upd_purchase_block & amount_as_item &
             const_commit & const_item & const_notes & const_buyer
            )]]] &
            const_listings & const_seller & const_timeout & from_seller & empty_acts).
    receive_simpl_goal.
    setoid_rewrite found_purchase.
    rewrite purchase_dispute; cbn.
    rewrite from_seller; cbn.
    rewrite empty_acts.
    setoid_rewrite found_item.
    apply Z.eqb_eq in amount_as_item; rewrite amount_as_item; cbn.
    rewrite const_seller, const_listings, const_timeout.
    rewrite const_commit, <- upd_purchase_block, <- seller_bit_rand, <- upd_purchase_counter,
            const_item, const_notes, const_buyer.
    destruct updated_purchase; destruct new_state; cbn.
    now setoid_rewrite <- updated_purchases. 
Qed.

Lemma buyer_abort_correct : forall chain ctx prev_state new_state new_acts purchaseId,
  EcommerceFixed.receive chain ctx prev_state (Some (buyer_abort purchaseId)) = Some (new_state, new_acts)
  <->
     (exists purchase updated_purchase item,
        FMap.find purchaseId prev_state.(purchases) = Some purchase
     /\ FMap.find purchaseId new_state.(purchases) = Some updated_purchase
     /\ FMap.find purchase.(itemId) prev_state.(listings) = Some item
     /\ (ctx.(ctx_from) =? purchase.(buyer))%address = true
     /\ new_acts = [act_transfer purchase.(buyer) item.(item_value)]

     /\ purchase.(purchase_state) = requested
     /\ updated_purchase.(purchase_state) = failed
     /\ updated_purchase.(commit) = purchase.(commit)
     /\ updated_purchase.(last_block) = purchase.(last_block)
     /\ updated_purchase.(itemId) = purchase.(itemId)
     /\ updated_purchase.(seller_bit) = purchase.(seller_bit)
     /\ updated_purchase.(notes) = purchase.(notes)
     /\ updated_purchase.(buyer) = purchase.(buyer)

     /\ new_state.(purchases) = FMap.add purchaseId updated_purchase prev_state.(purchases)
     )
  /\ prev_state.(listings) = new_state.(listings)
  /\ prev_state.(seller) = new_state.(seller)
  /\ prev_state.(timeout) = new_state.(timeout)
  .
Proof.
  intros *. split.
  - intros receive_some.
    receive_simpl receive_some.
    repeat split; try now inversion receive_some.
    remember ({|
    commit := commit p;
    last_block := last_block p;
    itemId := itemId p;
    seller_bit := seller_bit p;
    notes := notes p;
    purchase_state := failed;
    buyer := buyer p |})
    as updated_purchase.
    exists p, updated_purchase, i.
    repeat split; try now inversion Hequpdated_purchase.
    + inversion receive_some; cbn. apply FMap.find_add.
    + now apply purchase_state_eq_correct in E.
    + now inversion receive_some.
  - intros ([purchase [updated_purchase [item
            (found_purchase & upd_found_purchase & found_item & from_buyer & acts_transfer & purchase_req & upd_purchase_fail &
             const_commit & const_block & const_itemId & const_seller_bit & const_notes & const_buyer & updated_purchases)
            ]]] & (const_listings & const_seller & const_timeout)).
    receive_simpl_goal.
    setoid_rewrite found_purchase.
    rewrite purchase_req; cbn.
    rewrite from_buyer; cbn.
    setoid_rewrite found_item.
    rewrite acts_transfer.
    rewrite <- upd_purchase_fail.
    rewrite const_seller, const_listings, const_timeout.
    rewrite <- const_commit, <- const_block, <- const_itemId, <- const_seller_bit,
            <- const_notes, <- const_buyer.
    destruct updated_purchase; destruct new_state; cbn.
    now setoid_rewrite <- updated_purchases.
Qed.

Lemma buyer_confirm_delivery_correct : forall chain ctx prev_state new_state new_acts purchaseId,
  EcommerceFixed.receive chain ctx prev_state (Some (buyer_confirm_delivery purchaseId)) = Some (new_state, new_acts)
  <->
     (exists purchase updated_purchase item,
        FMap.find purchaseId prev_state.(purchases) = Some purchase
     /\ FMap.find purchaseId new_state.(purchases) = Some updated_purchase
     /\ FMap.find purchase.(itemId) prev_state.(listings) = Some item
     /\ (ctx.(ctx_from) =? purchase.(buyer))%address = true
     /\ new_acts = [act_transfer prev_state.(seller) item.(item_value)]

     /\ purchase.(purchase_state) = delivered
     /\ updated_purchase.(purchase_state) = completed
     /\ updated_purchase.(commit) = purchase.(commit)
     /\ updated_purchase.(last_block) = purchase.(last_block)
     /\ updated_purchase.(itemId) = purchase.(itemId)
     /\ updated_purchase.(seller_bit) = purchase.(seller_bit)
     /\ updated_purchase.(notes) = purchase.(notes)
     /\ updated_purchase.(buyer) = purchase.(buyer)

     /\ new_state.(purchases) = FMap.add purchaseId updated_purchase prev_state.(purchases)
     )
  /\ prev_state.(listings) = new_state.(listings)
  /\ prev_state.(seller) = new_state.(seller)
  /\ prev_state.(timeout) = new_state.(timeout)
  .
Proof.
  intros *. split.
  - intros receive_some.
    receive_simpl receive_some.
    repeat split; try now inversion receive_some.
    remember ({|
    commit := commit p;
    last_block := last_block p;
    itemId := itemId p;
    seller_bit := seller_bit p;
    notes := notes p;
    purchase_state := completed;
    buyer := buyer p |})
    as updated_purchase.
    exists p, updated_purchase, i.
    repeat split; try now inversion Hequpdated_purchase.
    + inversion receive_some; cbn. apply FMap.find_add.
    + now apply purchase_state_eq_correct in E.
    + now inversion receive_some.
  - intros ([purchase [updated_purchase [item
            (found_purchase & upd_found_purchase & found_item & from_buyer & acts_transfer & purchase_delivered & upd_purchase_completed &
             const_commit & const_block & const_itemId & const_seller_bit & const_notes & const_buyer & updated_purchases)
            ]]] & (const_listings & const_seller & const_timeout)).
    receive_simpl_goal.
    setoid_rewrite found_purchase.
    rewrite purchase_delivered; cbn.
    rewrite from_buyer; cbn.
    setoid_rewrite found_item.
    rewrite acts_transfer.
    rewrite <- upd_purchase_completed.
    rewrite const_seller, const_listings, const_timeout.
    rewrite <- const_commit, <- const_block, <- const_itemId, <- const_seller_bit,
            <- const_notes, <- const_buyer.
    destruct updated_purchase; destruct new_state; cbn.
    now setoid_rewrite <- updated_purchases.
Qed.


Lemma buyer_call_timeout_correct : forall chain ctx prev_state new_state new_acts purchaseId,
  EcommerceFixed.receive chain ctx prev_state (Some (buyer_call_timeout purchaseId)) = Some (new_state, new_acts)
  <->
     (exists purchase updated_purchase item,
        FMap.find purchaseId prev_state.(purchases) = Some purchase
     /\ FMap.find purchaseId new_state.(purchases) = Some updated_purchase
     /\ FMap.find purchase.(itemId) prev_state.(listings) = Some item
     /\ (ctx.(ctx_from) =? purchase.(buyer))%address = true
     /\ new_acts = [act_transfer purchase.(buyer) item.(item_value)]

     /\ (purchase.(purchase_state) = dispute \/ purchase.(purchase_state) = accepted)
     /\ (purchase.(last_block) + prev_state.(timeout) < chain.(current_slot))%nat
     /\ updated_purchase.(purchase_state) = failed
     /\ updated_purchase.(commit) = purchase.(commit)
     /\ updated_purchase.(last_block) = purchase.(last_block)
     /\ updated_purchase.(itemId) = purchase.(itemId)
     /\ updated_purchase.(seller_bit) = purchase.(seller_bit)
     /\ updated_purchase.(notes) = purchase.(notes)
     /\ updated_purchase.(buyer) = purchase.(buyer)

     /\ new_state.(purchases) = FMap.add purchaseId updated_purchase prev_state.(purchases)
     )
  /\ prev_state.(listings) = new_state.(listings)
  /\ prev_state.(seller) = new_state.(seller)
  /\ prev_state.(timeout) = new_state.(timeout)
  .
Proof.
  intros *. split.
  - intros receive_some.
    receive_simpl receive_some.
    repeat split; try now inversion receive_some.
    remember ({|
    commit := commit p;
    last_block := last_block p;
    itemId := itemId p;
    seller_bit := seller_bit p;
    notes := notes p;
    purchase_state := failed;
    buyer := buyer p |})
    as updated_purchase.
    exists p, updated_purchase, i.
    repeat split; try now inversion Hequpdated_purchase.
    + inversion receive_some; cbn. apply FMap.find_add.
    + apply orb_true_iff in E. destruct E as [purchase_st | purchase_st];
      apply purchase_state_eq_correct in purchase_st; easy.
    + now apply Nat.ltb_lt in E1.
    + now inversion receive_some.
  - intros ([purchase [updated_purchase [item
            (found_purchase & upd_found_purchase & found_item & from_buyer & acts_transfer & purchase_states & slot_gt_timeout & upd_purchase_fail &
             const_commit & const_block & const_itemId & const_seller_bit & const_notes & const_buyer & updated_purchases)
            ]]] & (const_listings & const_seller & const_timeout)).
    receive_simpl_goal.
    setoid_rewrite found_purchase.
    rewrite from_buyer; cbn.
    apply Nat.ltb_lt in slot_gt_timeout; rewrite slot_gt_timeout; cbn.
    destruct purchase_states as [p_state | p_state];
    rewrite p_state; cbn;
    setoid_rewrite found_item;
    rewrite acts_transfer;
    rewrite <- upd_purchase_fail;
    rewrite const_seller, const_listings, const_timeout;
    rewrite <- const_commit, <- const_block, <- const_itemId, <- const_seller_bit,
            <- const_notes, <- const_buyer;
    destruct updated_purchase; destruct new_state; cbn;
    now setoid_rewrite <- updated_purchases.
Qed.


Lemma seller_call_timeout_correct : forall chain ctx prev_state new_state new_acts purchaseId,
  EcommerceFixed.receive chain ctx prev_state (Some (seller_call_timeout purchaseId)) = Some (new_state, new_acts)
  <->
     (exists purchase updated_purchase item,
        FMap.find purchaseId prev_state.(purchases) = Some purchase
     /\ FMap.find purchaseId new_state.(purchases) = Some updated_purchase
     /\ FMap.find purchase.(itemId) prev_state.(listings) = Some item
     /\ new_acts = [act_transfer prev_state.(seller) item.(item_value)]

     /\ (purchase.(purchase_state) = delivered \/ purchase.(purchase_state) = counter)
     /\ (purchase.(last_block) + prev_state.(timeout) < chain.(current_slot))%nat
     /\ updated_purchase.(purchase_state) = completed
     /\ updated_purchase.(commit) = purchase.(commit)
     /\ updated_purchase.(last_block) = purchase.(last_block)
     /\ updated_purchase.(itemId) = purchase.(itemId)
     /\ updated_purchase.(seller_bit) = purchase.(seller_bit)
     /\ updated_purchase.(notes) = purchase.(notes)
     /\ updated_purchase.(buyer) = purchase.(buyer)

     /\ new_state.(purchases) = FMap.add purchaseId updated_purchase prev_state.(purchases)
     )
  
  /\ (ctx.(ctx_from) =? prev_state.(seller))%address = true
  /\ prev_state.(listings) = new_state.(listings)
  /\ prev_state.(seller) = new_state.(seller)
  /\ prev_state.(timeout) = new_state.(timeout)
  .
Proof.
  intros *. split.
  - intros receive_some.
    receive_simpl receive_some.
    repeat split; try now inversion receive_some.
    remember ({|
    commit := commit p;
    last_block := last_block p;
    itemId := itemId p;
    seller_bit := seller_bit p;
    notes := notes p;
    purchase_state := completed;
    buyer := buyer p |})
    as updated_purchase.
    exists p, updated_purchase, i.
    repeat split; try now inversion Hequpdated_purchase.
    + inversion receive_some; cbn. apply FMap.find_add.
    + apply orb_true_iff in E. destruct E as [purchase_st | purchase_st];
      apply purchase_state_eq_correct in purchase_st; easy.
    + now apply Nat.ltb_lt in E1.
    + now inversion receive_some.
  - intros ([purchase [updated_purchase [item
            (found_purchase & upd_found_purchase & found_item & acts_transfer & purchase_states & slot_gt_timeout & upd_purchase_completed &
             const_commit & const_block & const_itemId & const_seller_bit & const_notes & const_buyer & updated_purchases)
            ]]] & (from_buyer & const_listings & const_seller & const_timeout)).
    receive_simpl_goal.
    setoid_rewrite found_purchase.
    rewrite from_buyer; cbn.
    apply Nat.ltb_lt in slot_gt_timeout; rewrite slot_gt_timeout; cbn;
    destruct purchase_states as [p_state | p_state];
    rewrite p_state; cbn;
    setoid_rewrite found_item;
    rewrite acts_transfer;
    rewrite <- upd_purchase_completed;
    rewrite const_seller, const_listings, const_timeout;
    rewrite <- const_commit, <- const_block, <- const_itemId, <- const_seller_bit,
            <- const_notes, <- const_buyer;
    destruct updated_purchase; destruct new_state; cbn;
    now setoid_rewrite <- updated_purchases.
Qed.

Lemma seller_reject_contract_correct : forall chain ctx prev_state new_state new_acts purchaseId,
  EcommerceFixed.receive chain ctx prev_state (Some (seller_reject_contract purchaseId)) = Some (new_state, new_acts)
  <->
     (exists purchase updated_purchase item,
        FMap.find purchaseId prev_state.(purchases) = Some purchase
     /\ FMap.find purchaseId new_state.(purchases) = Some updated_purchase
     /\ FMap.find purchase.(itemId) prev_state.(listings) = Some item
     /\ new_acts = [act_transfer purchase.(buyer) item.(item_value)]

     /\ purchase.(purchase_state) = requested
     /\ updated_purchase.(purchase_state) = rejected
     /\ updated_purchase.(commit) = purchase.(commit)
     /\ updated_purchase.(last_block) = purchase.(last_block)
     /\ updated_purchase.(itemId) = purchase.(itemId)
     /\ updated_purchase.(seller_bit) = purchase.(seller_bit)
     /\ updated_purchase.(notes) = purchase.(notes)
     /\ updated_purchase.(buyer) = purchase.(buyer)

     /\ new_state.(purchases) = FMap.add purchaseId updated_purchase prev_state.(purchases)
     )
     
  /\ (ctx.(ctx_from) =? prev_state.(seller))%address = true
  /\ prev_state.(listings) = new_state.(listings)
  /\ prev_state.(seller) = new_state.(seller)
  /\ prev_state.(timeout) = new_state.(timeout)
  .
Proof.
  intros *. split.
  - intros receive_some.
    receive_simpl receive_some.
    repeat split; try now inversion receive_some.
    remember ({|
    commit := commit p;
    last_block := last_block p;
    itemId := itemId p;
    seller_bit := seller_bit p;
    notes := notes p;
    purchase_state := rejected;
    buyer := buyer p |})
    as updated_purchase.
    exists p, updated_purchase, i.
    repeat split; try now inversion Hequpdated_purchase.
    + inversion receive_some; cbn. apply FMap.find_add.
    + now apply purchase_state_eq_correct in E.
    + now inversion receive_some.
  - intros ([purchase [updated_purchase [item
            (found_purchase & upd_found_purchase & found_item & acts_transfer & purchase_requested & upd_purchase_rejected &
             const_commit & const_block & const_itemId & const_seller_bit & const_notes & const_buyer & updated_purchases)
            ]]] & (from_buyer & const_listings & const_seller & const_timeout)).
    receive_simpl_goal.
    setoid_rewrite found_purchase.
    rewrite purchase_requested; cbn.
    rewrite from_buyer; cbn.
    setoid_rewrite found_item.
    rewrite acts_transfer.
    rewrite <- upd_purchase_rejected.
    rewrite const_seller, const_listings, const_timeout.
    rewrite <- const_commit, <- const_block, <- const_itemId, <- const_seller_bit,
            <- const_notes, <- const_buyer.
    destruct updated_purchase; destruct new_state; cbn.
    now setoid_rewrite <- updated_purchases.
Qed.

Lemma seller_forfeit_dispute_correct : forall chain ctx prev_state new_state new_acts purchaseId,
  EcommerceFixed.receive chain ctx prev_state (Some (seller_forfeit_dispute purchaseId)) = Some (new_state, new_acts)
  <->
     (exists purchase updated_purchase item,
        FMap.find purchaseId prev_state.(purchases) = Some purchase
     /\ FMap.find purchaseId new_state.(purchases) = Some updated_purchase
     /\ FMap.find purchase.(itemId) prev_state.(listings) = Some item
     /\ new_acts = [act_transfer purchase.(buyer) item.(item_value)]

     /\ purchase.(purchase_state) = dispute
     /\ updated_purchase.(purchase_state) = failed
     /\ updated_purchase.(commit) = purchase.(commit)
     /\ updated_purchase.(last_block) = purchase.(last_block)
     /\ updated_purchase.(itemId) = purchase.(itemId)
     /\ updated_purchase.(seller_bit) = purchase.(seller_bit)
     /\ updated_purchase.(notes) = purchase.(notes)
     /\ updated_purchase.(buyer) = purchase.(buyer)

     /\ new_state.(purchases) = FMap.add purchaseId updated_purchase prev_state.(purchases)
     )
     
  /\ (ctx.(ctx_from) =? prev_state.(seller))%address = true
  /\ prev_state.(listings) = new_state.(listings)
  /\ prev_state.(seller) = new_state.(seller)
  /\ prev_state.(timeout) = new_state.(timeout)
  .
Proof.
  intros *. split.
  - intros receive_some.
    receive_simpl receive_some.
    repeat split; try now inversion receive_some.
    remember ({|
    commit := commit p;
    last_block := last_block p;
    itemId := itemId p;
    seller_bit := seller_bit p;
    notes := notes p;
    purchase_state := failed;
    buyer := buyer p |})
    as updated_purchase.
    exists p, updated_purchase, i.
    repeat split; try now inversion Hequpdated_purchase.
    + inversion receive_some; cbn. apply FMap.find_add.
    + now apply purchase_state_eq_correct in E.
    + now inversion receive_some.
  - intros ([purchase [updated_purchase [item
            (found_purchase & upd_found_purchase & found_item & acts_transfer & purchase_dispute & upd_purchase_failed &
             const_commit & const_block & const_itemId & const_seller_bit & const_notes & const_buyer & updated_purchases)
            ]]] & (from_buyer & const_listings & const_seller & const_timeout)).
    receive_simpl_goal.
    setoid_rewrite found_purchase.
    rewrite purchase_dispute; cbn.
    rewrite from_buyer; cbn.
    setoid_rewrite found_item.
    rewrite acts_transfer.
    rewrite <- upd_purchase_failed.
    rewrite const_seller, const_listings, const_timeout.
    rewrite <- const_commit, <- const_block, <- const_itemId, <- const_seller_bit,
            <- const_notes, <- const_buyer.
    destruct updated_purchase; destruct new_state; cbn.
    now setoid_rewrite <- updated_purchases.
Qed.

Lemma cons_to_app : forall {A} (a : A) (l : list A),
  a::l = [a] ++ l.
Proof. easy. Qed.

(* Proving correct for aux. function used in [seller_update_listings] *)
Lemma no_active_purchase_for_itemId_correct : forall state _itemId,
  no_active_purchase_for_itemId state _itemId = true
  <->
  Forall (fun '(_, purchase) => 
               purchase.(itemId) <> _itemId
            \/ purchase.(purchase_state) = completed
            \/ purchase.(purchase_state) = rejected
            \/ purchase.(purchase_state) = failed)
       (FMap.elements state.(purchases)).
Proof.
  intros *. split.
  - intros * no_active_purchase_true.
    unfold no_active_purchase_for_itemId in *.
    induction (FMap.elements state.(purchases)) as [| [purchaseId purchase] key_purchases]; auto.
    rewrite cons_to_app in no_active_purchase_true.
    rewrite filter_app in no_active_purchase_true; cbn in *.
    apply Forall_cons.
    + clear IHkey_purchases.
    (* Destruct appropriate purchase conditions. *)
      destruct ((purchase.(itemId) =? _itemId)%nat) eqn:is_itemId; cbn in *;
      destruct (purchase_state_eq purchase.(purchase_state) completed) eqn:state_completed;
      try apply purchase_state_eq_correct in state_completed;
      destruct (purchase_state_eq purchase.(purchase_state) rejected) eqn:state_rejected;
      try apply purchase_state_eq_correct in state_rejected;
      destruct (purchase_state_eq purchase.(purchase_state) failed) eqn:state_failed;
      try apply purchase_state_eq_correct in state_failed;
      cbn in *; try easy.
      * apply andb_true_iff in no_active_purchase_true; destruct no_active_purchase_true as [purchase_states _].
        destruct (purchase.(purchase_state)); try discriminate.
      * left. now apply beq_nat_false.
    + apply IHkey_purchases.
      (* Destruct appropriate purchase conditions. *)
      destruct ((purchase.(itemId) =? _itemId)%nat) eqn:is_itemId; cbn in *;
      destruct (purchase_state_eq purchase.(purchase_state) completed) eqn:state_completed;
      try apply purchase_state_eq_correct in state_completed;
      destruct (purchase_state_eq purchase.(purchase_state) rejected) eqn:state_rejected;
      try apply purchase_state_eq_correct in state_rejected;
      destruct (purchase_state_eq purchase.(purchase_state) failed) eqn:state_failed;
      try apply purchase_state_eq_correct in state_failed;
      cbn in *; try easy;
      (* Split boolean in no_active_purchase_true. *)
      apply andb_true_iff in no_active_purchase_true; destruct no_active_purchase_true as [H1 H2]; try easy.
  - intros forall_purchases.
    unfold no_active_purchase_for_itemId.
    induction (FMap.elements state.(purchases)) as [| [purchaseId purchase] key_purchases IH_key_purchases]; auto.
    rewrite cons_to_app in forall_purchases.
    apply Forall_app in forall_purchases.
    destruct ((purchase.(itemId) =? _itemId)%nat) eqn:is_itemId;
    cbn in *; rewrite is_itemId.
    + rewrite cons_to_app. 
      rewrite forallb_app. cbn in *. apply andb_true_iff. split.
      * apply andb_true_iff. split; auto.
        destruct forall_purchases as [H _].
        apply Forall_inv in H. destruct H as [neq_itemId | [p_state | [p_state | p_state]]];
        try now rewrite p_state.
        apply Nat.eqb_eq in is_itemId. lia.
      * now apply IH_key_purchases.
    + now apply IH_key_purchases.
Qed.


(* If item exists for _itemId, then all purchases belonging to that item should be of status [completed], [rejected] or [failed] *)
Lemma seller_update_listings_correct : forall chain ctx prev_state new_state new_acts _itemId upd_description upd_value,
  EcommerceFixed.receive chain ctx prev_state (Some (seller_update_listings _itemId upd_description upd_value)) = Some (new_state, new_acts)
  <->
  Forall (fun '(_, purchase) => 
               purchase.(itemId) <> _itemId
            \/ purchase.(purchase_state) = completed
            \/ purchase.(purchase_state) = rejected
            \/ purchase.(purchase_state) = failed)
       (FMap.elements prev_state.(purchases))
  /\ (ctx.(ctx_from) =? prev_state.(seller))%address = true
  /\ FMap.add _itemId {| item_value := upd_value; item_description := upd_description |} prev_state.(listings) = new_state.(listings)
  /\ prev_state.(purchases) = new_state.(purchases)
  /\ prev_state.(seller) = new_state.(seller)
  /\ prev_state.(timeout) = new_state.(timeout)
  /\ new_acts = []
  .
Proof.
  intros *. split.
  - intros receive_some.
    receive_simpl receive_some.
    repeat split; try now inversion receive_some.
    now apply no_active_purchase_for_itemId_correct.
  - intros (forall_purchases & from_seller & item_add &
            const_purchases & const_seller & const_timeout & empty_acts).
    receive_simpl_goal.
    rewrite from_seller; cbn.
    apply no_active_purchase_for_itemId_correct in forall_purchases.
    rewrite forall_purchases; cbn.
    rewrite item_add, const_seller, const_purchases, const_timeout, empty_acts.
    now destruct new_state.
Qed.


(* init correct *)
Lemma init_correct : forall state chain ctx setup,
  EcommerceFixed.init chain ctx setup = Some (state) ->
       (0 < setup.(setup_timeout))%nat
    /\ state.(timeout) = setup.(setup_timeout)
    /\ state.(listings) = setup.(setup_listings)
    /\ state.(seller) = ctx.(ctx_from)
    /\ state.(purchases) = FMap.empty.
Proof.
  intros * init_some.
  receive_simpl init_some. inversion init_some; cbn.
  now apply Nat.ltb_lt in E.
Qed.


Ltac apply_message_lemma H :=
  match type of H with
  | _ _ _ _ (Some (buyer_request_purchase _ _)) = Some (_, _) =>
      apply buyer_request_purchase_correct in H
  | _ _ _ _ (Some (buyer_abort _)) = Some (_, _) =>
      apply buyer_abort_correct in H
  | _ _ _ _ (Some (buyer_confirm_delivery _)) = Some (_, _) =>
      apply buyer_confirm_delivery_correct in H
  | _ _ _ _ (Some (buyer_dispute_delivery _ _)) = Some (_, _) =>
      apply buyer_dispute_delivery_correct in H
  | _ _ _ _ (Some (buyer_call_timeout _)) = Some (_, _) =>
      apply buyer_call_timeout_correct in H
  | _ _ _ _ (Some (buyer_open_commitment _ _ _)) = Some (_, _) =>
      apply buyer_open_commitment_correct in H
  | _ _ _ _ (Some (seller_call_timeout _)) = Some (_, _) =>
      apply seller_call_timeout_correct in H
  | _ _ _ _ (Some (seller_reject_contract _)) = Some (_, _) =>
      apply seller_reject_contract_correct in H
  | _ _ _ _ (Some (seller_accept_contract _)) = Some (_, _) =>
      apply seller_accept_contract_correct in H
  | _ _ _ _ (Some (seller_item_was_delivered _)) = Some (_, _) =>
      apply seller_item_was_delivered_correct in H
  | _ _ _ _ (Some (seller_forfeit_dispute _)) = Some (_, _) =>
      apply seller_forfeit_dispute_correct in H
  | _ _ _ _ (Some (seller_counter_dispute _ _)) = Some (_, _) =>
      apply seller_counter_dispute_correct in H
  | _ _ _ _ (Some (seller_update_listings _ _ _)) = Some (_, _) =>
      apply seller_update_listings_correct in H
  end.

(* [seller] and [timeout] never changes on receive. *)
Lemma seller_timeout_constant_on_receive : forall chain ctx msg prev_state new_state new_acts,
  EcommerceFixed.receive chain ctx prev_state msg = Some (new_state, new_acts) ->
       prev_state.(seller) = new_state.(seller)
    /\ prev_state.(timeout) = new_state.(timeout).
Proof.
  intros * receive_some.
  destruct_message; now apply_message_lemma receive_some.
Qed.



(* [timeout] in the state is always equal to [setup_timeout] from deployment. *)
Lemma timeout_constants chain_state contract_address (trace : ChainTrace empty_state chain_state) :
  env_contracts chain_state contract_address = Some (contract : WeakContract) ->
  exists deploy_info cstate,
    deployment_info _ trace contract_address = Some deploy_info
    /\ contract_state chain_state contract_address = Some cstate
    /\ let setup := deploy_info.(deployment_setup) in
        cstate.(timeout) = setup.(setup_timeout).
Proof.
  apply (lift_dep_info_contract_state_prop contract); intros *.
  - intros init_some. apply init_correct in init_some; auto.
    cbn. now inversion init_some.
  - intros IH receive_some.
    destruct_message; apply_message_lemma receive_some; auto; easy.
Qed.

(*Lemma test : forall {K V} (m : FMap K V) (new_key : K) (new_value : V),
  42 = 42.
  Forall f (FMap.elements m) ->
  Forall f (FMap.elements).
Lemma purchase_buyer_is_never_contract_addr : forall chain_state contract_address,
  reachable chain_state ->
  env_contracts chain_state contract_address = Some (contract : WeakContract) ->
  exists contract_state,
  Forall (
    fun '(_, purchase) =>
      purchase.(buyer) <> contract_address
  ) (FMap.elements contract_state.(purchases)).
Proof.
  contract_induction; intros; auto.
  - apply init_correct in init_some; auto.
    destruct_hyps. rewrite H3. admit.
  - destruct_message; apply_message_lemma receive_some; auto.
    + destruct_hyps. rewrite H6. cbn. destruct new_state; cbn in *. easy.
Lemma no_self_calls : forall chain_state contract_address,
  reachable chain_state ->
  env_contracts chain_state contract_address = Some (contract : WeakContract) ->
  Forall (
    fun act_body =>
      match act_body with
      | act_transfer to _ => (to =? contract_address)%address = false
      | _ => False
      end) (outgoing_acts chain_state contract_address).
Proof.
  contract_induction; intros; auto.
  - now inversion IH.
  - apply Forall_app. split; auto.
    clear IH.
    (*instantiate (CallFacts := fun _ ctx state _ _ => 
        state.(seller <> ctx_contract_address ctx)
    /\ fundDeposit state <> ctx_contract_address ctx).*)

    destruct_message; apply_message_lemma receive_some; auto;
    try now rewrite_var receive_some new_acts.
    + destruct_hyps.
    + destruct_hyps. destruct receive_some. destruct H. destruct H. destruct H.
     rewrite_var H new_acts. cbn.
    try now rewrite_var receive_some new_acts.
    + apply_message_lemma receive_some.
    now rewrite_var receive_some new_acts test. repeat_split_H receive_some.
    repeat_rewrite_H receive_some.
      destruct receive_some as [H1 H2]. destruct H2 as [H3 H4].
       destruct H4 as [H5 H6]. destruct H6 as [H7 H8].
       destruct H8 as [H9 H10]. easy.
       destruct H1. destruct H2.
    repeat_split_H receive_some. destruct H3. repeat_split_H H3. easy.
    repeat_split_H H2. repeat_split_H H2. easy.
      assert (OK : new_acts = [] ). { easy. } rewr easy.
      pose proof (new_acts = []) as [OK].
      assert (OK : new_acts = [] ). { easy. } destruct receive_some. easy. apply buyer_request_purchase_correct in receive_some.
      destruct receive_some. destruct H0. destruct H1. destruct H2. destruct H3. easy. rewrite H4. cbn. easy.
    
*)
  
(* If timeout has reached for an active [Purchase], it is possible for someone to end the contract. *)
End Theories.