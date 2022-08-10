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

Ltac receive_simpl_step g :=
  match type of g with
  | context[find_purchase] => unfold find_purchase in g; cbn in g
  | context[find_item] => unfold find_item in g; cbn in g
  | context[purchase_exists] => unfold purchase_exists in g; cbn in g
  | context[FMap.find _ ?v] => destruct (FMap.find _ v) eqn:?; cbn in g
  | context[setter_from_getter_State_purchases] => unfold setter_from_getter_State_purchases in g; cbn in g
  | context[set_State_purchases] => unfold set_State_purchases in g; cbn in g
  | context[setter_from_getter_Purchase_last_block] => unfold setter_from_getter_Purchase_last_block in g; cbn in g
  | context[set_Purchase_last_block] => unfold set_Purchase_last_block in g; cbn in g
  | context[setter_from_getter_Purchase_purchase_state] => unfold setter_from_getter_Purchase_purchase_state in g; cbn in g
  | context[set_Purchase_purchase_state] => unfold set_Purchase_purchase_state in g; cbn in g
  | context[setter_from_getter_Purchase_seller_bit] => unfold setter_from_getter_Purchase_seller_bit in g; cbn in g
  | context[set_Purchase_seller_bit] => unfold set_Purchase_seller_bit in g; cbn in g
  | context[required_true ?cond] => destruct cond eqn:?E; inversion E; cbn in g
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
  end. 

Tactic Notation "receive_simpl_goal" := cbn; repeat (receive_simpl_goal_step; cbn).

Open Scope Z.
  
Lemma purchase_state_eq_correct : forall (state1 state2 : PurchaseState),
  state1 = state2 <-> purchase_state_eq state1 state2 = true.
Proof.
  intros *. split; intros; destruct state1; destruct state2; try discriminate; reflexivity.
Qed.

Lemma buyer_request_purchase_contract_correct : forall chain ctx prev_state new_state new_acts _itemId _notes,
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

Lemma seller_counter_dispute : forall chain ctx prev_state new_state new_acts id random_bit,
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

End Theories.