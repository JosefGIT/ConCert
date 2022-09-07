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
From Coq Require Import Permutation.

Section Theories.

Context `{Base : ChainBase}. 

Arguments hash_bid : simpl never.
Arguments hash_purchaseId : simpl never.


Ltac destruct_message :=
  match goal with
  | receive_some : context[receive _ _ _ _ ?msg = Some (_, _)] |- _ => destruct msg as [?m|]; try discriminate; destruct m
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
  | context[required_amount_zero _] => unfold required_amount_zero in g; cbn in g
  | context[required_no_self_call _] => unfold required_no_self_call in g; cbn in g

  | context[setter_from_getter_State_purchases] => unfold setter_from_getter_State_purchases in g; cbn in g
  | context[set_State_purchases] => unfold set_State_purchases in g; cbn in g
  | context[setter_from_getter_Purchase_last_block] => unfold setter_from_getter_Purchase_last_block in g; cbn in g
  | context[set_Purchase_last_block] => unfold set_Purchase_last_block in g; cbn in g
  | context[setter_from_getter_Purchase_purchase_state] => unfold setter_from_getter_Purchase_purchase_state in g; cbn in g
  | context[set_Purchase_purchase_state] => unfold set_Purchase_purchase_state in g; cbn in g
  | context[setter_from_getter_Purchase_seller_bit] => unfold setter_from_getter_Purchase_seller_bit in g; cbn in g
  | context[set_Purchase_seller_bit] => unfold set_Purchase_seller_bit in g; cbn in g
  | context[setter_from_getter_Purchase_pool] => unfold setter_from_getter_Purchase_pool in g; cbn in g
  | context[set_Purchase_pool] => unfold set_Purchase_pool in g; cbn in g
  | context[setter_from_getter_State_listings] => unfold setter_from_getter_State_listings in g; cbn in g
  | context[set_State_listings] => unfold set_State_listings in g; cbn in g
  | context[setter_from_getter_Purchase_discarded_money] => unfold setter_from_getter_Purchase_discarded_money in g; cbn in g
  | context[set_Purchase_discarded_money] => unfold set_Purchase_discarded_money in g; cbn in g
  end. 
  
Tactic Notation "receive_simpl" constr(g) := cbn in g; repeat (receive_simpl_step g); try discriminate.

Ltac receive_simpl_goal_step :=
  match goal with
  | |- context[find_purchase] => unfold find_purchase
  | |- context[find_item] => unfold find_item
  | |- context[purchase_exists] => unfold purchase_exists
  | |- context[purchase_state_eq] => unfold purchase_state_eq
  | |- context[required_amount_zero _] => unfold required_amount_zero
  | |- context[required_no_self_call _] => unfold required_no_self_call
  
  | |- context[setter_from_getter_State_purchases] => unfold setter_from_getter_State_purchases
  | |- context[set_State_purchases] => unfold set_State_purchases
  | |- context[setter_from_getter_Purchase_last_block] => unfold setter_from_getter_Purchase_last_block
  | |- context[set_Purchase_last_block] => unfold set_Purchase_last_block
  | |- context[setter_from_getter_Purchase_purchase_state] => unfold setter_from_getter_Purchase_purchase_state
  | |- context[set_Purchase_purchase_state] => unfold set_Purchase_purchase_state
  | |- context[setter_from_getter_Purchase_seller_bit] => unfold setter_from_getter_Purchase_seller_bit
  | |- context[set_Purchase_seller_bit] => unfold set_Purchase_seller_bit
  | |- context[setter_from_getter_Purchase_pool] => unfold setter_from_getter_Purchase_pool
  | |- context[set_Purchase_pool] => unfold set_Purchase_pool
  | |- context[setter_from_getter_State_listings] => unfold setter_from_getter_State_listings
  | |- context[set_State_listings] => unfold set_State_listings
  | |- context[setter_from_getter_Purchase_discarded_money] => unfold setter_from_getter_Purchase_discarded_money
  | |- context[set_Purchase_discarded_money] => unfold set_Purchase_discarded_money
  end. 

Tactic Notation "receive_simpl_goal" := cbn; repeat (receive_simpl_goal_step; cbn).

Open Scope Z.
  
Lemma address_eqb_eq : forall (addr1 addr2 : Address),
  (addr1 =? addr2)%address = true <-> addr1 = addr2.
Proof.
  intros *. split; intros H; destruct (address_eqb_spec addr1 addr2); easy.
Qed.

Lemma purchase_state_eq_correct : forall (state1 state2 : PurchaseState),
  state1 = state2 <-> purchase_state_eq state1 state2 = true.
Proof.
  intros *. split; intros; destruct state1; destruct state2; try discriminate; reflexivity.
Qed.

(*Lemma address_eq_ne' `{ChainBase} x y :
  address_eqb x y = false ->
  x <> y.
Proof. intros. destruct_address_eq; auto. Qed. destruct (address_eqb_spec x y) as [->|]; tauto. Qed.
*)
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
      /\ new_purchase.(pool) = ctx.(ctx_amount)
      /\ new_purchase.(last_block) = chain.(current_slot)
      /\ new_purchase.(purchase_state) = requested
      /\ new_purchase.(buyer) = ctx.(ctx_from)
      /\ new_purchase.(seller_bit) = false
      /\ new_purchase.(commit) = 0%N
      /\ new_purchase.(notes) = _notes
      /\ new_purchase.(discarded_money) = 0)
  /\ ctx.(ctx_from) <> ctx.(ctx_contract_address)
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
    buyer := ctx_from ctx;
    pool := ctx_amount ctx |})
    as new_purchase.
    repeat split; try now inversion receive_some.
    + exists i. repeat split; try now inversion receive_some.
      now apply Z.eqb_eq in E.
    + remember (hash_purchaseId chain.(current_slot) ctx.(ctx_from)) as new_purchaseId.
      exists new_purchaseId, new_purchase.
      repeat split; try now inversion Heqnew_purchase.
      now inversion receive_some.
    + destruct_address_eq; auto.
  - intros ([item (prev_item & new_item & amount_sent)] &
            (purchaseId & new_purchase & purchaseId_hash & not_found_purchase & purchase_added & purchase_itemId & purchase_pool & purchase_last_block &
             ppurchase_state & purchase_buyer & purchase_seller_bit & purchase_commit & purchase_notes & purchase_disc_money) &
             not_caddr & const_listings & const_seller & const_timeout & empty_acts).
    receive_simpl_goal.
    apply address_eq_ne in not_caddr.
    rewrite not_caddr; cbn.
    setoid_rewrite prev_item.
    apply Z.eqb_eq in amount_sent. rewrite amount_sent; cbn.
    rewrite <- purchaseId_hash.
    setoid_rewrite not_found_purchase; cbn.
    rewrite empty_acts.
    rewrite const_listings, const_seller, const_timeout.
    rewrite <- purchase_last_block, <- purchase_commit, <- purchase_itemId, <- purchase_pool, <- purchase_seller_bit,
            <- purchase_notes, <- purchase_disc_money, <- ppurchase_state, <- purchase_buyer.   
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
      /\ updated_purchase.(pool) = purchase.(pool)
      /\ updated_purchase.(discarded_money) = purchase.(discarded_money)
      /\ new_state.(purchases) = FMap.add id updated_purchase prev_state.(purchases))
  /\ ctx.(ctx_from) = prev_state.(seller)
  /\ ctx.(ctx_amount) = 0
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
      buyer := buyer p;
      pool := pool p |})
    as updated_purchase.
    inversion receive_some; clear receive_some. cbn. repeat split.
    exists p, updated_purchase. repeat split; try now inversion Hequpdated_purchase.
    + now apply purchase_state_eq_correct in E.
    + apply FMap.find_add.
    + now apply address_eqb_eq.
    + now apply Z.eqb_eq in E1.
  - intros ([purchase [updated_purchase (purchase_found & state_requested & updated_purchase_found &
                updated_state_accepted & block_current & commit_constant & item_constant &
                seller_bit_constant & notes_constant & buyer_constant & pool_constant & disc_constant & purchase_added)]] &
             ctx_from_seller & amount_zero & listings_constant & seller_constant & timeout_constant & no_acts).
    receive_simpl_goal.
    rewrite amount_zero; cbn.
    setoid_rewrite purchase_found.
    rewrite state_requested; cbn.
    apply address_eqb_eq in ctx_from_seller. rewrite ctx_from_seller; cbn.
    rewrite no_acts; cbn.
    rewrite seller_constant, listings_constant, timeout_constant.
    rewrite <- updated_state_accepted, <- block_current, <- commit_constant, <- item_constant,
            <- seller_bit_constant, <- notes_constant, <- buyer_constant, <- pool_constant, <- disc_constant.
            auto.
    destruct updated_purchase; destruct new_state; cbn in *.
    now setoid_rewrite <- purchase_added.
Qed.

Lemma buyer_dispute_delivery_correct : forall chain ctx prev_state new_state new_acts id commitment,
  EcommerceFixed.receive chain ctx prev_state (Some (buyer_dispute_delivery id commitment)) = Some (new_state, new_acts)
  <->
  (exists purchase updated_purchase item,
     FMap.find id prev_state.(purchases) = Some purchase
  /\ FMap.find purchase.(itemId) prev_state.(listings) = Some item
  /\ ctx.(ctx_from) = purchase.(buyer)
  /\ purchase.(purchase_state) = delivered
  /\ updated_purchase.(purchase_state) = dispute
  /\ updated_purchase.(pool) = purchase.(pool) + item.(item_value)
  /\ updated_purchase.(last_block) = chain.(current_slot)
  /\ new_state.(purchases) = FMap.add id updated_purchase prev_state.(purchases)
  /\ commitment = updated_purchase.(commit)
  (* These fields should stay constant *)
  /\ purchase.(itemId) = updated_purchase.(itemId)
  /\ purchase.(seller_bit) = updated_purchase.(seller_bit)
  /\ purchase.(notes) = updated_purchase.(notes)
  /\ purchase.(buyer) = updated_purchase.(buyer)
  /\ purchase.(discarded_money) = updated_purchase.(discarded_money)
  /\ ctx.(ctx_amount) = item.(item_value))
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
    buyer := buyer p;
    pool := pool p + i.(item_value);
    discarded_money := discarded_money p |})
    as updated_purchase.
    repeat split; try now inversion receive_some.
    exists p, updated_purchase, i.
    repeat split; try now inversion Hequpdated_purchase.
    + now apply address_eqb_eq.
    + now apply purchase_state_eq_correct in E0.
    + now inversion receive_some.
    + now apply Z.eqb_eq in E.
  - intros ([purchase [updated_purchase [item
            (purchase_found & item_found & purchase_from & state_delivered & upd_state_dispute & upd_pool & block_current &
             upd_purchases & com & const_item & const_seller_bit & const_notes & const_buyer & const_disc & amount_item_value)
            ]]] & (const_listings & const_seller & const_timeout & acts_empty)).
  receive_simpl_goal.
  setoid_rewrite purchase_found.
  setoid_rewrite item_found.
  apply Z.eqb_eq in amount_item_value; rewrite amount_item_value; cbn.
  rewrite state_delivered; cbn.
  apply address_eqb_eq in purchase_from; rewrite purchase_from; cbn.
  rewrite acts_empty.

  rewrite const_item, const_seller_bit, const_notes, const_buyer,
          const_disc, const_listings, const_seller, const_timeout,
          com, <- upd_state_dispute, <- block_current, <- upd_pool.
  destruct updated_purchase; destruct new_state;
  now setoid_rewrite <- upd_purchases.
Qed.

Lemma buyer_open_commitment_correct : forall chain ctx prev_state new_state new_acts id buyer_bit nonce,
  EcommerceFixed.receive chain ctx prev_state (Some (buyer_open_commitment id buyer_bit nonce)) = Some (new_state, new_acts)
  <->
  (exists purchase updated_purchase item,
     FMap.find id prev_state.(purchases) = Some purchase
  /\ FMap.find purchase.(itemId) prev_state.(listings) = Some item
  /\ FMap.find id new_state.(purchases) = Some updated_purchase
  /\ new_state.(purchases) = FMap.add id updated_purchase prev_state.(purchases)
  /\ failed = updated_purchase.(purchase_state)
  /\ 0 = updated_purchase.(pool)
  /\ item.(item_value) = updated_purchase.(discarded_money)
  /\ purchase.(last_block) = updated_purchase.(last_block)
  /\ purchase.(commit) = updated_purchase.(commit)
  /\ purchase.(itemId) = updated_purchase.(itemId)
  /\ purchase.(seller_bit) = updated_purchase.(seller_bit)
  /\ purchase.(notes) = updated_purchase.(notes)
  /\ purchase.(buyer) = updated_purchase.(buyer)
  /\ purchase.(purchase_state) = counter
  /\ hash_bid id buyer_bit nonce = purchase.(commit)
  /\ ctx.(ctx_from) = purchase.(buyer)
  /\ (eqb purchase.(seller_bit) buyer_bit = true
     -> new_acts = [act_transfer purchase.(buyer) (purchase.(pool) - item.(item_value))])
  /\ (eqb purchase.(seller_bit) buyer_bit = false
     -> new_acts = [act_transfer prev_state.(seller) (purchase.(pool) - item.(item_value))])
  )
  /\ ctx.(ctx_amount) = 0
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
    buyer := buyer p;
    pool := 0 |})
    as updated_purchase.
    repeat split; try now inversion Hequpdated_purchase; try now inversion receive_some.
    exists p, updated_purchase, i.
    repeat split; try now inversion Hequpdated_purchase.
    + inversion receive_some; cbn. apply FMap.find_add.
    + now inversion receive_some.
    + now apply purchase_state_eq_correct in E0.
    + now apply N.eqb_eq in E1.
    + now apply address_eqb_eq.
    + intros eq_bits. inversion receive_some. rewrite eq_bits. now rewrite H0.
    + intros neq_bits. inversion receive_some. now rewrite neq_bits.
    + now apply Z.eqb_eq in E2. 
  - intros ([purchase [updated_purchase [item 
            (purchase_found & item_found & updated_purchase_found & purchases_updated & upd_purchase_failed & pool_zero & const_disc &
             const_block & const_commit & const_itemId & const_seller_bit & const_notes & const_buyer &
             purchase_counter & correct_hash & ctx_from_buyer & eq_bits & neq_bits)]]] &
             (amount_zero & const_listings & const_seller & const_timeout)).
    receive_simpl_goal.
    rewrite amount_zero; cbn.
    setoid_rewrite purchase_found.
    setoid_rewrite item_found.
    apply address_eqb_eq in ctx_from_buyer.
    rewrite ctx_from_buyer; cbn. 
    rewrite purchase_counter; cbn.
    apply N.eqb_eq in correct_hash; rewrite correct_hash; cbn.
    rewrite const_seller, const_listings, const_timeout.
    rewrite const_commit, const_disc, const_block,
            const_seller_bit,const_notes, const_itemId, const_buyer.
    rewrite upd_purchase_failed.
    rewrite pool_zero.
    destruct updated_purchase; destruct new_state; cbn in *.
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
   /\ purchase.(buyer) = updated_purchase.(buyer)
   /\ purchase.(pool) = updated_purchase.(pool)
   /\ purchase.(discarded_money) = updated_purchase.(discarded_money))
  /\ ctx.(ctx_amount) = 0
  /\ prev_state.(listings) = new_state.(listings)
  /\ prev_state.(seller) = new_state.(seller)
  /\ prev_state.(timeout) = new_state.(timeout)

  /\ ctx.(ctx_from) = prev_state.(seller)
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
    buyer := buyer p;
    pool := pool p |})
    as updated_purchase.
    exists p, updated_purchase.
    repeat split; try now inversion Hequpdated_purchase; try now inversion receive_some.
    + inversion receive_some; cbn. apply FMap.find_add.
    + now inversion receive_some.
    + now apply purchase_state_eq_correct in E.
    + now apply Z.eqb_eq in E1.
    + now apply address_eqb_eq.
  - intros ([purchase [updated_purchase
            (found_purchase & found_upd_purchase & purchases_updated & purchase_accepted & upd_purchase_delivered & upd_purchase_block &
             const_commit & const_item & const_seller_bit & const_notes & const_buyer & const_pool & const_disc)]] &
            amount_zero & const_listings & const_seller & const_timeout & from_seller & empty_acts).
    receive_simpl_goal.
    rewrite amount_zero; cbn.
    setoid_rewrite found_purchase.
    rewrite purchase_accepted; cbn.
    apply address_eqb_eq in from_seller; rewrite from_seller; cbn. 
    rewrite const_seller, const_listings, const_timeout.
    rewrite const_commit, const_item, const_notes, const_seller_bit, const_buyer, const_pool, const_disc.
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
   /\ purchase.(pool) + item.(item_value) = updated_purchase.(pool)
   (* These should remain constant *)
   /\ purchase.(discarded_money) = updated_purchase.(discarded_money)
   /\ purchase.(commit) = updated_purchase.(commit)
   /\ purchase.(itemId) = updated_purchase.(itemId)
   /\ purchase.(notes) = updated_purchase.(notes)
   /\ purchase.(buyer) = updated_purchase.(buyer))
  /\ prev_state.(listings) = new_state.(listings)
  /\ prev_state.(seller) = new_state.(seller)
  /\ prev_state.(timeout) = new_state.(timeout)

  /\ ctx.(ctx_from) = prev_state.(seller)
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
    buyer := buyer p;
    pool := pool p + ctx_amount ctx |})
    as updated_purchase.
    exists p, updated_purchase, i.
    repeat split; try now inversion Hequpdated_purchase.
    + inversion receive_some; cbn. apply FMap.find_add.
    + now inversion receive_some.
    + now apply purchase_state_eq_correct in E.
    + now apply Z.eqb_eq in E1.
    + inversion Hequpdated_purchase; cbn. now apply Z.eqb_eq in E1.
    + now apply address_eqb_eq.
  - intros ([purchase [updated_purchase [item (
             found_purchase & found_upd_purchase & found_item & updated_purchases & purchase_dispute &
             seller_bit_rand & upd_purchase_counter & upd_purchase_block & amount_as_item & upd_pool &
             const_disc & const_commit & const_item & const_notes & const_buyer
            )]]] &
            const_listings & const_seller & const_timeout & from_seller & empty_acts).
    receive_simpl_goal.
    setoid_rewrite found_purchase.
    rewrite purchase_dispute; cbn.
    apply address_eqb_eq in from_seller; rewrite from_seller; cbn.
    rewrite empty_acts.
    setoid_rewrite found_item.
    (* pose proof (Z.eqb_eq _ _ amount_as_item). *)
    (* pose proof not working for some reason, therefore applying twice. *)
    apply Z.eqb_eq in amount_as_item; rewrite amount_as_item; cbn.
    apply Z.eqb_eq in amount_as_item; rewrite amount_as_item; cbn.
    rewrite const_seller, const_listings, const_timeout.
    rewrite const_commit, const_disc, <- upd_purchase_block, <- seller_bit_rand, <- upd_purchase_counter,
            const_item, const_notes, const_buyer, upd_pool.
    destruct updated_purchase; destruct new_state; cbn.
    now setoid_rewrite <- updated_purchases. 
Qed.

Lemma buyer_abort_correct : forall chain ctx prev_state new_state new_acts purchaseId,
  EcommerceFixed.receive chain ctx prev_state (Some (buyer_abort purchaseId)) = Some (new_state, new_acts)
  <->
     (exists purchase updated_purchase,
        FMap.find purchaseId prev_state.(purchases) = Some purchase
     /\ FMap.find purchaseId new_state.(purchases) = Some updated_purchase
     /\ ctx.(ctx_from) = purchase.(buyer)
     /\ new_acts = [act_transfer purchase.(buyer) purchase.(pool)]

     /\ purchase.(purchase_state) = requested
     /\ updated_purchase.(purchase_state) = failed
     /\ updated_purchase.(pool) = 0
     /\ updated_purchase.(commit) = purchase.(commit)
     /\ updated_purchase.(last_block) = purchase.(last_block)
     /\ updated_purchase.(itemId) = purchase.(itemId)
     /\ updated_purchase.(seller_bit) = purchase.(seller_bit)
     /\ updated_purchase.(notes) = purchase.(notes)
     /\ updated_purchase.(buyer) = purchase.(buyer)
     /\ updated_purchase.(discarded_money) = purchase.(discarded_money)

     /\ new_state.(purchases) = FMap.add purchaseId updated_purchase prev_state.(purchases)
     )
  /\ ctx.(ctx_amount) = 0
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
    buyer := buyer p;
    pool := 0 |})
    as updated_purchase.
    exists p, updated_purchase.
    repeat split; try now inversion Hequpdated_purchase.
    + inversion receive_some; cbn. apply FMap.find_add.
    + now apply address_eqb_eq. 
    + now apply purchase_state_eq_correct in E.
    + now inversion receive_some.
    + now apply Z.eqb_eq in E1.
  - intros ([purchase [updated_purchase
            (found_purchase & upd_found_purchase & from_buyer & acts_transfer & purchase_req & upd_purchase_fail & upd_pool_zero &
             const_commit & const_block & const_itemId & const_seller_bit & const_notes & const_buyer & const_disc & updated_purchases)
            ]] & (amount_zero & const_listings & const_seller & const_timeout)).
    receive_simpl_goal.
    rewrite amount_zero; cbn.
    setoid_rewrite found_purchase.
    rewrite purchase_req; cbn.
    apply address_eqb_eq in from_buyer; rewrite from_buyer; cbn.
    rewrite acts_transfer.
    rewrite <- upd_purchase_fail, <- upd_pool_zero.
    rewrite const_seller, const_listings, const_timeout.
    rewrite <- const_commit, <- const_block, <- const_itemId, <- const_seller_bit,
            <- const_notes, <- const_buyer, <- const_disc.
    destruct updated_purchase; destruct new_state; cbn.
    now setoid_rewrite <- updated_purchases.
Qed.

Lemma buyer_confirm_delivery_correct : forall chain ctx prev_state new_state new_acts purchaseId,
  EcommerceFixed.receive chain ctx prev_state (Some (buyer_confirm_delivery purchaseId)) = Some (new_state, new_acts)
  <->
     (exists purchase updated_purchase,
        FMap.find purchaseId prev_state.(purchases) = Some purchase
     /\ FMap.find purchaseId new_state.(purchases) = Some updated_purchase
     /\ ctx.(ctx_from) = purchase.(buyer)
     /\ new_acts = [act_transfer prev_state.(seller) purchase.(pool)]

     /\ purchase.(purchase_state) = delivered
     /\ updated_purchase.(purchase_state) = completed
     /\ updated_purchase.(pool) = 0
     /\ updated_purchase.(commit) = purchase.(commit)
     /\ updated_purchase.(last_block) = purchase.(last_block)
     /\ updated_purchase.(itemId) = purchase.(itemId)
     /\ updated_purchase.(seller_bit) = purchase.(seller_bit)
     /\ updated_purchase.(notes) = purchase.(notes)
     /\ updated_purchase.(buyer) = purchase.(buyer)
     /\ updated_purchase.(discarded_money) = purchase.(discarded_money)

     /\ new_state.(purchases) = FMap.add purchaseId updated_purchase prev_state.(purchases)
     )
  /\ ctx.(ctx_amount) = 0
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
    buyer := buyer p;
    pool := 0 |})
    as updated_purchase.
    exists p, updated_purchase.
    repeat split; try now inversion Hequpdated_purchase.
    + inversion receive_some; cbn. apply FMap.find_add.
    + now apply address_eqb_eq.
    + now apply purchase_state_eq_correct in E.
    + now inversion receive_some.
    + now apply Z.eqb_eq in E1.
  - intros ([purchase [updated_purchase
            (found_purchase & upd_found_purchase & from_buyer & acts_transfer & purchase_delivered & upd_purchase_completed & upd_pool_zero &
             const_commit & const_block & const_itemId & const_seller_bit & const_notes & const_buyer & const_disc & updated_purchases)
            ]] & (amount_zero & const_listings & const_seller & const_timeout)).
    receive_simpl_goal.
    rewrite amount_zero; cbn.
    setoid_rewrite found_purchase.
    rewrite purchase_delivered; cbn.
    apply address_eqb_eq in from_buyer; rewrite from_buyer; cbn.
    rewrite acts_transfer.
    rewrite <- upd_purchase_completed, <- upd_pool_zero.
    rewrite const_seller, const_listings, const_timeout.
    rewrite <- const_commit, <- const_block, <- const_itemId, <- const_seller_bit,
            <- const_notes, <- const_buyer, <- const_disc.
    destruct updated_purchase; destruct new_state; cbn.
    now setoid_rewrite <- updated_purchases.
Qed.


Lemma buyer_call_timeout_correct : forall chain ctx prev_state new_state new_acts purchaseId,
  EcommerceFixed.receive chain ctx prev_state (Some (buyer_call_timeout purchaseId)) = Some (new_state, new_acts)
  <->
     (exists purchase updated_purchase,
        FMap.find purchaseId prev_state.(purchases) = Some purchase
     /\ FMap.find purchaseId new_state.(purchases) = Some updated_purchase
     /\ ctx.(ctx_from) = purchase.(buyer)
     /\ new_acts = [act_transfer purchase.(buyer) purchase.(pool)]

     /\ (purchase.(purchase_state) = dispute \/ purchase.(purchase_state) = accepted)
     /\ (purchase.(last_block) + prev_state.(timeout) < chain.(current_slot))%nat
     /\ updated_purchase.(pool) = 0
     /\ updated_purchase.(purchase_state) = failed
     /\ updated_purchase.(commit) = purchase.(commit)
     /\ updated_purchase.(last_block) = purchase.(last_block)
     /\ updated_purchase.(itemId) = purchase.(itemId)
     /\ updated_purchase.(seller_bit) = purchase.(seller_bit)
     /\ updated_purchase.(notes) = purchase.(notes)
     /\ updated_purchase.(buyer) = purchase.(buyer)
     /\ updated_purchase.(discarded_money) = purchase.(discarded_money)

     /\ new_state.(purchases) = FMap.add purchaseId updated_purchase prev_state.(purchases)
     )
  /\ ctx.(ctx_amount) = 0
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
    buyer := buyer p;
    pool := 0 |})
    as updated_purchase.
    exists p, updated_purchase.
    repeat split; try now inversion Hequpdated_purchase.
    + inversion receive_some; cbn. apply FMap.find_add.
    + now apply address_eqb_eq.
    + apply orb_true_iff in E. destruct E as [purchase_st | purchase_st];
      apply purchase_state_eq_correct in purchase_st; easy.
    + now apply Nat.ltb_lt in E1.
    + now inversion receive_some.
    + now apply Z.eqb_eq in E2.
  - intros ([purchase [updated_purchase
            (found_purchase & upd_found_purchase & from_buyer & acts_transfer & purchase_states & slot_gt_timeout & upd_pool_zero & upd_purchase_fail &
             const_commit & const_block & const_itemId & const_seller_bit & const_notes & const_buyer & const_disc & updated_purchases)
            ]] & (amount_zero & const_listings & const_seller & const_timeout)).
    receive_simpl_goal.
    rewrite amount_zero; cbn.
    setoid_rewrite found_purchase.
    apply address_eqb_eq in from_buyer; rewrite from_buyer; cbn.
    apply Nat.ltb_lt in slot_gt_timeout; rewrite slot_gt_timeout; cbn.
    destruct purchase_states as [p_state | p_state];
    rewrite p_state; cbn;
    rewrite acts_transfer;
    rewrite <- upd_purchase_fail, <- upd_pool_zero;
    rewrite const_seller, const_listings, const_timeout;
    rewrite <- const_commit, <- const_block, <- const_itemId, <- const_seller_bit,
            <- const_notes, <- const_buyer, <- const_disc;
    destruct updated_purchase; destruct new_state; cbn;
    now setoid_rewrite <- updated_purchases.
Qed.


Lemma seller_call_timeout_correct : forall chain ctx prev_state new_state new_acts purchaseId,
  EcommerceFixed.receive chain ctx prev_state (Some (seller_call_timeout purchaseId)) = Some (new_state, new_acts)
  <->
     (exists purchase updated_purchase,
        FMap.find purchaseId prev_state.(purchases) = Some purchase
     /\ FMap.find purchaseId new_state.(purchases) = Some updated_purchase
     /\ new_acts = [act_transfer prev_state.(seller) purchase.(pool)]

     /\ (purchase.(purchase_state) = delivered \/ purchase.(purchase_state) = counter)
     /\ (purchase.(last_block) + prev_state.(timeout) < chain.(current_slot))%nat
     /\ updated_purchase.(purchase_state) = completed
     /\ updated_purchase.(pool) = 0
     /\ updated_purchase.(commit) = purchase.(commit)
     /\ updated_purchase.(last_block) = purchase.(last_block)
     /\ updated_purchase.(itemId) = purchase.(itemId)
     /\ updated_purchase.(seller_bit) = purchase.(seller_bit)
     /\ updated_purchase.(notes) = purchase.(notes)
     /\ updated_purchase.(buyer) = purchase.(buyer)
     /\ updated_purchase.(discarded_money) = purchase.(discarded_money)

     /\ new_state.(purchases) = FMap.add purchaseId updated_purchase prev_state.(purchases)
     )
  
  /\ ctx.(ctx_from) = prev_state.(seller)
  /\ ctx.(ctx_amount) = 0
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
    buyer := buyer p;
    pool := 0 |})
    as updated_purchase.
    exists p, updated_purchase.
    repeat split; try now inversion Hequpdated_purchase.
    + inversion receive_some; cbn. apply FMap.find_add.
    + apply orb_true_iff in E. destruct E as [purchase_st | purchase_st];
      apply purchase_state_eq_correct in purchase_st; easy.
    + now apply Nat.ltb_lt in E1.
    + now inversion receive_some.
    + now apply address_eqb_eq.
    + now apply Z.eqb_eq in E2.
  - intros ([purchase [updated_purchase
            (found_purchase & upd_found_purchase & acts_transfer & purchase_states & slot_gt_timeout & upd_purchase_completed & upd_pool_zero &
             const_commit & const_block & const_itemId & const_seller_bit & const_notes & const_buyer & const_disc & updated_purchases)
            ]] & (from_buyer & amount_zero & const_listings & const_seller & const_timeout)).
    receive_simpl_goal.
    rewrite amount_zero; cbn.
    setoid_rewrite found_purchase.
    apply address_eqb_eq in from_buyer; rewrite from_buyer; cbn.
    apply Nat.ltb_lt in slot_gt_timeout; rewrite slot_gt_timeout; cbn;
    destruct purchase_states as [p_state | p_state];
    rewrite p_state; cbn;
    rewrite acts_transfer;
    rewrite <- upd_purchase_completed, <- upd_pool_zero;
    rewrite const_seller, const_listings, const_timeout;
    rewrite <- const_commit, <- const_block, <- const_itemId, <- const_seller_bit,
            <- const_notes, <- const_buyer, <- const_disc;
    destruct updated_purchase; destruct new_state; cbn;
    now setoid_rewrite <- updated_purchases.
Qed.

Lemma seller_reject_contract_correct : forall chain ctx prev_state new_state new_acts purchaseId,
  EcommerceFixed.receive chain ctx prev_state (Some (seller_reject_contract purchaseId)) = Some (new_state, new_acts)
  <->
     (exists purchase updated_purchase,
        FMap.find purchaseId prev_state.(purchases) = Some purchase
     /\ FMap.find purchaseId new_state.(purchases) = Some updated_purchase
     /\ new_acts = [act_transfer purchase.(buyer) purchase.(pool)]

     /\ purchase.(purchase_state) = requested
     /\ updated_purchase.(purchase_state) = rejected
     /\ updated_purchase.(pool) = 0
     /\ updated_purchase.(commit) = purchase.(commit)
     /\ updated_purchase.(last_block) = purchase.(last_block)
     /\ updated_purchase.(itemId) = purchase.(itemId)
     /\ updated_purchase.(seller_bit) = purchase.(seller_bit)
     /\ updated_purchase.(notes) = purchase.(notes)
     /\ updated_purchase.(buyer) = purchase.(buyer)
     /\ updated_purchase.(discarded_money) = purchase.(discarded_money)

     /\ new_state.(purchases) = FMap.add purchaseId updated_purchase prev_state.(purchases)
     )
     
  /\ ctx.(ctx_from) = prev_state.(seller)
  /\ ctx.(ctx_amount) = 0
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
    buyer := buyer p;
    pool := 0 |})
    as updated_purchase.
    exists p, updated_purchase.
    repeat split; try now inversion Hequpdated_purchase.
    + inversion receive_some; cbn. apply FMap.find_add.
    + now apply purchase_state_eq_correct in E.
    + now inversion receive_some.
    + now apply address_eqb_eq.
    + now apply Z.eqb_eq in E1.
  - intros ([purchase [updated_purchase
            (found_purchase & upd_found_purchase & acts_transfer & purchase_requested & upd_purchase_rejected & upd_pool_zero &
             const_commit & const_block & const_itemId & const_seller_bit & const_notes & const_buyer & const_disc & updated_purchases)
            ]] & (from_buyer & amount_zero & const_listings & const_seller & const_timeout)).
    receive_simpl_goal.
    rewrite amount_zero; cbn.
    setoid_rewrite found_purchase.
    rewrite purchase_requested; cbn.
    apply address_eqb_eq in from_buyer; rewrite from_buyer; cbn.
    rewrite acts_transfer.
    rewrite <- upd_purchase_rejected, <- upd_pool_zero.
    rewrite const_seller, const_listings, const_timeout.
    rewrite <- const_commit, <- const_block, <- const_itemId, <- const_seller_bit,
            <- const_notes, <- const_buyer, <- const_disc.
    destruct updated_purchase; destruct new_state; cbn.
    now setoid_rewrite <- updated_purchases.
Qed.

Lemma seller_forfeit_dispute_correct : forall chain ctx prev_state new_state new_acts purchaseId,
  EcommerceFixed.receive chain ctx prev_state (Some (seller_forfeit_dispute purchaseId)) = Some (new_state, new_acts)
  <->
     (exists purchase updated_purchase,
        FMap.find purchaseId prev_state.(purchases) = Some purchase
     /\ FMap.find purchaseId new_state.(purchases) = Some updated_purchase
     /\ new_acts = [act_transfer purchase.(buyer) purchase.(pool)]

     /\ purchase.(purchase_state) = dispute
     /\ updated_purchase.(purchase_state) = failed
     /\ updated_purchase.(pool) = 0
     /\ updated_purchase.(commit) = purchase.(commit)
     /\ updated_purchase.(last_block) = purchase.(last_block)
     /\ updated_purchase.(itemId) = purchase.(itemId)
     /\ updated_purchase.(seller_bit) = purchase.(seller_bit)
     /\ updated_purchase.(notes) = purchase.(notes)
     /\ updated_purchase.(buyer) = purchase.(buyer)
     /\ updated_purchase.(discarded_money) = purchase.(discarded_money)

     /\ new_state.(purchases) = FMap.add purchaseId updated_purchase prev_state.(purchases)
     )
     
  /\ ctx.(ctx_from) = prev_state.(seller)
  /\ ctx.(ctx_amount) = 0
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
    buyer := buyer p;
    pool := 0 |})
    as updated_purchase.
    exists p, updated_purchase.
    repeat split; try now inversion Hequpdated_purchase.
    + inversion receive_some; cbn. apply FMap.find_add.
    + now apply purchase_state_eq_correct in E.
    + now inversion receive_some.
    + now apply address_eqb_eq.
    + now apply Z.eqb_eq in E1.
  - intros ([purchase [updated_purchase
            (found_purchase & upd_found_purchase & acts_transfer & purchase_dispute & upd_purchase_failed & upd_pool_zero &
             const_commit & const_block & const_itemId & const_seller_bit & const_notes & const_buyer & const_disc & updated_purchases)
            ]] & (from_buyer & amount_zero & const_listings & const_seller & const_timeout)).
    receive_simpl_goal.
    rewrite amount_zero; cbn.
    setoid_rewrite found_purchase.
    rewrite purchase_dispute; cbn.
    apply address_eqb_eq in from_buyer; rewrite from_buyer; cbn.
    rewrite acts_transfer.
    rewrite <- upd_purchase_failed, <- upd_pool_zero.
    rewrite const_seller, const_listings, const_timeout.
    rewrite <- const_commit, <- const_block, <- const_itemId, <- const_seller_bit,
            <- const_notes, <- const_buyer, <- const_disc.
    destruct updated_purchase; destruct new_state; cbn.
    now setoid_rewrite <- updated_purchases.
Qed.

Lemma cons_to_app : forall {A} (a : A) (l : list A),
  a::l = [a] ++ l.
Proof. easy. Qed.

(* TODO?: Refactor ugly proof. *)
(* Proving correct for aux. function used in [seller_update_listings] *)

(* FIX PROOF DO NOT DELETE!! *)
Lemma no_active_purchase_for_itemId_correct : forall state _itemId,
  no_active_purchase_for_itemId state _itemId = true
  <->
  Forall (fun '(_, purchase) => 
               purchase.(itemId) <> _itemId
            \/ purchase.(purchase_state) = completed
            \/ purchase.(purchase_state) = rejected
            \/ purchase.(purchase_state) = failed)
       (FMap.elements state.(purchases)).
Proof. Admitted.
(* DO NOT DELETE BELOW!! *)
  (*
  intros *. split.
  - intros * no_active_purchase_true.
    unfold no_active_purchase_for_itemId in *.
    induction (FMap.values state.(purchases)) as [| purchase purchases]; auto.
    rewrite cons_to_app in no_active_purchase_true.
    rewrite filter_app in no_active_purchase_true; cbn in *.
    apply Forall_cons.
    + clear IHpurchases.
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
    + apply IHpurchases.
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
    induction (FMap.values state.(purchases)) as [| purchase key_purchases IHpurchases]; auto.
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
      * now apply IHpurchases.
    + now apply IHpurchases.
Qed.
*)

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
  /\ 0 <= upd_value
  /\ new_state.(purchases) = prev_state.(purchases)
  /\ new_state.(seller) = prev_state.(seller)
  /\ new_state.(timeout) = prev_state.(timeout)
  /\ ctx.(ctx_amount) = 0
  /\ new_acts = []
  .
Proof.
  intros *. split.
  - intros receive_some.
    receive_simpl receive_some.
    repeat split; try now inversion receive_some.
    + now apply no_active_purchase_for_itemId_correct.
    + now apply Z.leb_le in E.
    + now apply Z.eqb_eq in E2.
  - intros (forall_purchases & from_seller & item_add & value_gt_zero &
            const_purchases & const_seller & const_timeout & amount_zero & empty_acts).
    receive_simpl_goal.
    rewrite amount_zero; cbn.
    apply Z.leb_le in value_gt_zero; rewrite value_gt_zero; cbn.
    rewrite from_seller; cbn.
    apply no_active_purchase_for_itemId_correct in forall_purchases.
    rewrite forall_purchases; cbn.
    rewrite item_add, <- const_seller, <- const_purchases, <- const_timeout, empty_acts.
    now destruct new_state.
Qed.


(* init correct *)
Lemma init_correct : forall state chain ctx setup,
  EcommerceFixed.init chain ctx setup = Some (state) ->
       (0 < setup.(setup_timeout))%nat
    /\ ctx.(ctx_amount) = 0
    /\ state.(timeout) = setup.(setup_timeout)
    /\ state.(listings) = setup.(setup_listings)
    /\ state.(seller) = ctx.(ctx_from)
    /\ state.(purchases) = FMap.empty
    /\ ctx.(ctx_from) <> ctx.(ctx_contract_address).
Proof.
  intros * init_some.
  receive_simpl init_some. inversion init_some; cbn.
  apply Z.eqb_eq in E0.
  apply Nat.ltb_lt in E.
  repeat split; auto.
  destruct_address_eq; auto.
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

(**** START  --  FINITE MAP LEMMAS ****)
From stdpp Require gmap.
Lemma map_Forall_to_list_2 : forall {K V : Type} `{countable.Countable K} (m : FMap K V) (P : (K * V) -> Prop),
  fin_maps.map_Forall (prod_uncurry P) m <-> Forall P (FMap.elements m).
Proof.
  intros *. split; intros HForall.
  - apply Forall_forall. intros [i x] ix_in_m.
    apply base.elem_of_list_In in ix_in_m. rewrite fin_maps.elem_of_map_to_list in ix_in_m. now apply (HForall i x).
  - intros i x find_some. rewrite Forall_forall in HForall. rewrite <- fin_maps.elem_of_map_to_list in find_some. apply HForall. now rewrite <- base.elem_of_list_In.
Qed.

Lemma Forall_elements_add : forall {K V : Type} `{countable.Countable K} (m : FMap K V) (f : (K*V) -> Prop) (new_key : K) (new_value : V),
  f (new_key, new_value) ->
  Forall f (FMap.elements m) ->
  Forall f (FMap.elements (FMap.add new_key new_value m)).
Proof.
  intros * new_satisfied m_satisfied.
  apply map_Forall_to_list_2; auto.
  apply map_Forall_to_list_2 in m_satisfied.
  apply fin_maps.map_Forall_insert_2; auto.
Qed.


Lemma val_in_map_In_key_val : forall {K V : Type} `{countable.Countable K} (m : FMap K V) (v : V),
  In v (FMap.values m) -> exists (k : K), In (k, v) (FMap.elements m).
Proof.
  intros *.
  unfold FMap.values. induction (FMap.elements m) as [| [k' v'] vals' IH]; intros v_in_m.
  - easy.
  - cbn in *. destruct v_in_m.
    + subst. now exists k'.
    + destruct IH; auto. now exists x.
Qed. 

Lemma key_val_in_map_In_val : forall {K V : Type} `{countable.Countable K} (m : FMap K V) (k : K) (v : V),
  In (k, v) (FMap.elements m) -> In v (FMap.values m).
Proof.
  intros *.
  unfold FMap.values. induction (FMap.elements m) as [| [k' v'] vals' IH]; intros kv_in_m; cbn in *.
  - easy.
  - destruct kv_in_m as [kv_eq | kv_in_vals'].
    + now inversion kv_eq.
    + right. now apply IH.
Qed. 

Lemma Forall_elements_values : forall {K V : Type} `{countable.Countable K} (m : FMap K V) (f : V -> Prop),
  Forall (fun '(_, v) => f v) (FMap.elements m) <-> Forall f (FMap.values m).
Proof.
  intros *. split; intros forall_m.
  - rewrite Forall_forall in *. intros v v_in_m.
    apply val_in_map_In_key_val in v_in_m.
    destruct v_in_m as [k' in_m]. now apply (forall_m (k', v)).
  - rewrite Forall_forall in *. intros [k' v'] k'v'_in_m.
    apply forall_m. now apply key_val_in_map_In_val in k'v'_in_m.
Qed.

Lemma Forall_values_add : forall {K V : Type} `{countable.Countable K} (m : FMap K V) (f : V -> Prop) (new_key : K) (new_value : V),
  f new_value ->
  Forall f (FMap.values m) ->
  Forall f (FMap.values (FMap.add new_key new_value m)).
Proof.
  intros * new_satisfied m_satisfied.
  rewrite <- Forall_elements_values in *.
  now apply Forall_elements_add.
Qed.

Lemma In_values_find_some : forall {K V : Type} `{countable.Countable K} (m : FMap K V) (v : V),
  In v (FMap.values m) -> exists k, FMap.find k m = Some v.
Proof.
  intros * kv_in_m. apply val_in_map_In_key_val in kv_in_m.
  destruct kv_in_m as [k' kv_in_m].
  exists k'. now apply FMap.In_elements.
Qed.

Lemma find_some_In_values : forall {K V : Type} `{countable.Countable K} (m : FMap K V) (k : K) (v : V),
  FMap.find k m = Some v -> In v (FMap.values m).
Proof.
  intros * find_some.
  apply FMap.In_elements in find_some.
  now apply key_val_in_map_In_val in find_some.
Qed.
(**** END  --  FINITE MAP LEMMAS ****)

Ltac no_facts_added :=
  instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True);
  instantiate (DeployFacts := fun _ _ => True);
  instantiate (CallFacts := fun _ _ _ _ _ => True);
  unset_all; subst; cbn in *;
  destruct_chain_step; auto;
  destruct_action_eval; auto.

Lemma seller_timeout_never_changes_after_init : forall chain_state contract_address (trace : ChainTrace empty_state chain_state),
  reachable chain_state ->
  env_contracts chain_state contract_address = Some (contract : WeakContract) ->
  exists deploy_info contr_state,
     deployment_info _ trace contract_address = Some deploy_info
  /\ contract_state chain_state contract_address = Some contr_state
  /\ let setup := deploy_info.(deployment_setup) in
     let setup_seller := deploy_info.(deployment_from) in
        contr_state.(timeout) = setup.(setup_timeout)
     /\ contr_state.(seller) = setup_seller.
Proof. 
  contract_induction; intros; auto.
  - apply init_correct in init_some; auto.
    destruct_hyps. now destruct result; cbn in *; subst.
  - destruct_message; apply_message_lemma receive_some; destruct_hyps; auto; easy.
  - destruct_message; apply_message_lemma receive_some; destruct_hyps; auto; easy.
  - no_facts_added.
Qed.

(* Aux. lemma *)
Lemma sum_pool_discarded_add : forall (purchases : purchases_type) (id : N) (purchase1 purchase2 : Purchase),
  FMap.find id purchases = Some purchase1 ->
  sumZ (fun '(_, purchase) => purchase.(pool) + purchase.(discarded_money)) (FMap.elements (FMap.add id purchase2 purchases))=
  sumZ (fun '(_, purchase) => purchase.(pool) + purchase.(discarded_money)) (FMap.elements purchases) - (purchase1.(pool) + purchase1.(discarded_money)) + (purchase2.(pool) + purchase2.(discarded_money)).
Proof.
  intros * p_found.
  assert (perm1 : Permutation (FMap.elements (FMap.add id purchase2 purchases)) ((id, purchase2)::(FMap.elements (FMap.remove id purchases))) ).
  { now eapply FMap.elements_add_existing. }
  rewrite (sumZ_permutation perm1); cbn.
  assert (perm2 : Permutation (FMap.elements (FMap.add id purchase1 purchases)) ((id, purchase1)::(FMap.elements (FMap.remove id purchases))) ).
  { now eapply FMap.elements_add_existing. }
  rewrite <- (FMap.add_id id purchase1 purchases p_found).
  setoid_rewrite (sumZ_permutation perm2); cbn.
  (* undo a rewrite *)
  rewrite (FMap.add_id id purchase1 purchases p_found).
  lia.
Qed.

Lemma seller_not_contract_addr chain_state caddr:
  reachable chain_state ->
  env_contracts chain_state caddr = Some (contract : WeakContract) ->
  exists cstate,
       contract_state chain_state caddr = Some cstate
    /\ cstate.(seller) <> caddr.
Proof.
  contract_induction; intros; auto.
  - apply init_correct in init_some; auto. now destruct_hyps.
  - destruct_message; apply_message_lemma receive_some; destruct_hyps; auto; congruence.
  - destruct_message; apply_message_lemma receive_some; destruct_hyps; auto; congruence.
  - no_facts_added.
Qed. 

Lemma Forall_elements_f : forall {K V : Type} `{countable.Countable K} (m : FMap K V) (f : (K*V) -> Prop) (k : K) (v : V),
  FMap.find k m = Some v ->
  Forall f (FMap.elements m) ->
  f (k, v).
Proof.
  intros * found_some forall_elements.
  apply map_Forall_to_list_2 in forall_elements.
  apply (fin_maps.map_Forall_lookup_1 (prod_uncurry f) m k v); auto.
Qed.

Lemma Forall_elements_f_remove : forall {K V : Type} `{countable.Countable K} (m : FMap K V) (f : (K*V) -> Prop) (k : K),
  Forall f (FMap.elements m) ->
  Forall f (FMap.elements (FMap.remove k m)).
Proof.
Admitted.

Lemma buyer_not_caddr_update : forall ctx id purchase1 purchase2 (purchases : purchases_type),
  purchase1.(buyer) <> ctx.(ctx_contract_address) ->
  purchase1.(buyer) = purchase2.(buyer) ->
  FMap.find id purchases = Some purchase1 ->
  Forall (fun '(_, p) => p.(buyer) <> ctx.(ctx_contract_address)) (FMap.elements purchases) ->
  Forall (fun '(_, p) => p.(buyer) <> ctx.(ctx_contract_address)) (FMap.elements (FMap.add id purchase2 purchases)).
Proof.
  intros * buyer_neq_caddr buyer_eq purchase_found forall_purchases.
  assert (perm1: Permutation (FMap.elements (FMap.add id purchase2 purchases)) ((id, purchase2)::(FMap.elements (FMap.remove id purchases))) ).
  { now eapply FMap.elements_add_existing. }
  rewrite perm1. apply Forall_cons; auto.
  - now rewrite <- buyer_eq. 
  - now apply Forall_elements_f_remove.
Qed.

Lemma buyers_not_contract_addr chain_state caddr:
  reachable chain_state ->
  env_contracts chain_state caddr = Some (contract : WeakContract) ->
  exists cstate,
       contract_state chain_state caddr = Some cstate
    /\ Forall (fun '(_, p) => p.(buyer) <> caddr) (FMap.elements cstate.(purchases)).
Proof.
  contract_induction; intros; auto.
  - apply init_correct in init_some; auto. destruct_hyps.
    rewrite H4. setoid_rewrite FMap.elements_empty. easy.
  - destruct_message; apply_message_lemma receive_some; destruct_hyps; auto;
    try(
        match goal with
        | [H : new_state.(purchases) = _ |- _] => rewrite H
        end
    ); cbn;
    try (eapply (buyer_not_caddr_update _ _ x x0); auto; now apply (Forall_elements_f _ _ id x) in IH); auto.
    (* request_purchase *)
    assert (perm : Permutation (FMap.elements (FMap.add x x0 (purchases prev_state))) ((x, x0)::(FMap.elements prev_state.(purchases)))). { now apply FMap.elements_add. }
    setoid_rewrite perm. apply Forall_cons; auto.
    now rewrite H12.
    (* almost identical to non-recursive calls *)
  - destruct_message; apply_message_lemma receive_some; destruct_hyps; auto;
    try(
        match goal with
        | [H : new_state.(purchases) = _ |- _] => rewrite H
        end
    ); cbn;
    try (eapply (buyer_not_caddr_update _ _ x x0); auto; now apply (Forall_elements_f _ _ id x) in IH); auto.
    (* request_purchase *)
    assert (perm : Permutation (FMap.elements (FMap.add x x0 (purchases prev_state))) ((x, x0)::(FMap.elements prev_state.(purchases)))). { now apply FMap.elements_add. }
    setoid_rewrite perm. apply Forall_cons; auto.
  - no_facts_added.
Qed. 

(** Ecommerce never calls itself or sends transactions to itself. *)
Lemma no_self_calls bstate caddr :
  reachable bstate ->
  env_contracts bstate caddr = Some (EcommerceFixed.contract : WeakContract) ->
  Forall (fun act_body =>
    match act_body with
    | act_transfer to _ => (to =? caddr)%address = false
    | _ => False
    end) (outgoing_acts bstate caddr).
Proof.
  contract_induction; intros; auto.
  - now inversion IH.
  - instantiate (CallFacts := fun _ ctx state _ _ =>
      state.(seller) <> ctx_contract_address ctx /\ Forall (fun '(_, p) => p.(buyer) <> ctx_contract_address ctx) (FMap.elements state.(purchases))).
    unfold CallFacts in facts.
    destruct facts as [f1 f2].
    apply address_eq_ne in from_other.
    apply address_eq_ne in f1.
    apply Forall_app; split; auto.
    destruct_message; apply_message_lemma receive_some; destruct_hyps; auto;
    try(
      match goal with
      | [H : new_acts = _ |- _] => rewrite H
      end
    ); auto.
    + constructor; auto. now rewrite <- H5.
    + constructor; auto. now rewrite <- H5.
    + destruct (eqb (x.(seller_bit)) buyer_bit).
      * rewrite H19; auto. constructor; auto. now rewrite <- H18.
      * rewrite H20; auto.
    + constructor; auto. apply (Forall_elements_f _ _ id x) in f2; auto; cbn in *.
      now apply address_eq_ne in f2.
    + constructor; auto. apply (Forall_elements_f _ _ id x) in f2; auto; cbn in *.
      now apply address_eq_ne in f2.
  - inversion_clear IH as [|? ? head_not_me tail_not_me].
    apply Forall_app. split; auto.
    destruct head; try contradiction.
    destruct action_facts as [? [? ?]].
    destruct_address_eq; congruence.
  - now rewrite <- perm.
  - instantiate (DeployFacts := fun _ _ => True).
    instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
    unset_all; subst.
    destruct_chain_step; auto.
    destruct_action_eval; auto.
    intros * contract_dep ?. cbn. split.
    + apply seller_not_contract_addr in contract_dep.
      * now destruct_hyps.  
      * now constructor.
    + apply buyers_not_contract_addr in contract_dep.
      * now destruct_hyps.  
      * now constructor.
Qed.

Lemma no_self_calls' : forall bstate origin from_addr to_addr amount msg acts,
  reachable bstate ->
  env_contracts bstate to_addr = Some (contract : WeakContract) ->
  chain_state_queue bstate = {|
    act_origin := origin;
    act_from := from_addr;
    act_body :=
      match msg with
      | Some msg => act_call to_addr amount msg
      | None => act_transfer to_addr amount
      end
  |} :: acts ->
  from_addr <> to_addr.
Proof.
  intros * reach deployed queue.
  apply no_self_calls in deployed as no_self_calls; auto.
  unfold outgoing_acts in no_self_calls.
  rewrite queue in no_self_calls.
  cbn in no_self_calls.
  destruct_address_eq; auto.
  inversion_clear no_self_calls as [|? ? hd _].
  destruct msg.
  * congruence.
  * now rewrite address_eq_refl in hd.
Qed.


Ltac no_self_calls_solve := now instantiate (CallFacts := fun _ ctx _ _ _ => ctx_from ctx <> ctx_contract_address ctx).
Ltac destruct_apply_msg receive_some := destruct_message; apply_message_lemma receive_some; destruct_hyps; auto.
Lemma purchase_discarded_zero_when_not_failed : forall chain_state contract_addr,
  reachable chain_state ->
  env_contracts chain_state contract_addr = Some (contract : WeakContract) ->
  exists cstate,
       contract_state chain_state contract_addr = Some cstate
    /\ Forall (fun '(_, purchase) => purchase.(purchase_state) <> failed -> purchase.(discarded_money) = 0)
       (FMap.elements cstate.(purchases)).
Proof.
  contract_induction; intros; auto.
  - apply init_correct in init_some; auto; destruct_hyps. rewrite H4. now setoid_rewrite FMap.elements_empty.
  - destruct_apply_msg receive_some.
    + assert (perm : Permutation (FMap.elements (FMap.add x x0 (purchases prev_state))) ((x, x0)::(FMap.elements prev_state.(purchases)))). { now apply FMap.elements_add.  }
      rewrite perm.

Lemma contract_balance_is_pool_and_discarded_sum : forall chain_state contract_addr,
  reachable chain_state ->
  env_contracts chain_state contract_addr = Some (contract : WeakContract) ->
  exists cstate,
     contract_state chain_state contract_addr = Some cstate
  /\ sumZ (fun '(_, purchase) => purchase.(pool) + purchase.(discarded_money)) (FMap.elements cstate.(purchases)) = env_account_balances chain_state contract_addr - (sumZ (fun act => act_body_amount act) (outgoing_acts chain_state contract_addr)).
Proof.
  contract_induction; intros; auto; only 1-4 : cbn in *.
  - apply init_correct in init_some; auto. destruct_hyps. now rewrite H4, H0.
  - rewrite IH. lia.
  - destruct_message; apply_message_lemma receive_some; destruct_hyps; auto;
    try(
      match goal with
      | [H : purchases new_state = FMap.add _ _ (purchases prev_state) |- _] => rewrite H
      end
    );
    try(
      match goal with
      | [H : new_acts = [] |- _] => rewrite H
      end
    ); cbn;
    try (rewrite (sum_pool_discarded_add prev_state.(purchases) id x x0) by auto;
    subst; cbn; rewrite IH; lia).
    + assert (perm : Permutation (FMap.elements (FMap.add x x0 (purchases prev_state))) ((x, x0)::(FMap.elements prev_state.(purchases)))). { now apply FMap.elements_add.  }
      rewrite (sumZ_permutation perm); cbn.
      rewrite H9, H16.
      now setoid_rewrite IH.
    + destruct (eqb (x.(seller_bit)) (buyer_bit)); rewrite (sum_pool_discarded_add prev_state.(purchases) id x x0) by auto.
      * rewrite H19 by auto. rewrite IH. rewrite H0. cbn. rewrite <- H8, <- H9. cbn.
      rewrite IH. rewrite H0. cbn. lia.
        rewrite IH. rewrite H0. cbn. lia.
        rewrite IH. cbn. lia. admit. (* lia.*)
      * rewrite H20 by auto. cbn. lia.
    + rewrite H3. subst. cbn. rewrite IH. lia.
  - no_self_calls_solve.
  - now rewrite <- perm.
  - instantiate (DeployFacts := fun _ _ => True).
    instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
    unset_all; subst.
    destruct_chain_step; auto.
    destruct_action_eval; auto.
    intros * contr_deployed ?. cbn.
    subst.
    eapply no_self_calls'; eauto.
    now constructor.
Qed.
(* If timeout has reached for an active [Purchase], it is possible for someone to end the contract. *)
(* All item values are greater than 0. *)
End Theories.