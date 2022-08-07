From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Examples.Ecommerce Require Import Ecommerce.
Require Import NArith.

Local Open Scope string_scope.

Instance showN : Show N :=
{
  show (n : N) :=  show (N.to_nat n)
}.

Derive Show for Msg.
Derive Show for PurchaseState.

Instance showItem : Show Item :=
{
    show item := 
           "Item{"
        ++ "item_value: " ++ show item.(item_value) ++ sep
        ++ "item_description: " ++ show item.(item_description)
        ++ "}"
}.
Instance showSetup : Show Setup :=
{
    show setup :=
           "Setup{"
        ++ "setup_listings: " ++ show setup.(setup_listings) ++ sep
        ++ "setup_timeout: " ++ show setup.(setup_timeout)
        ++ "}"
}.


Instance showPurchase : Show Purchase :=
{
    show purchase :=
        "Purchase{"
     ++ "commit: " ++ show purchase.(commit) ++ sep
     ++ "last_block: " ++ show purchase.(last_block) ++ sep
     ++ "item: " ++ show purchase.(item) ++ sep
     ++ "seller_bit: " ++ show purchase.(seller_bit) ++ sep
     ++ "notes: " ++ show purchase.(notes) ++ sep
     ++ "purchase_state: " ++ show purchase.(purchase_state) ++ sep
     ++ "buyer: " ++ show purchase.(buyer)
     ++ "}"
}.

Instance showState : Show State :=
{
    show state := 
        "State{"
     ++ "seller: " ++ show state.(seller) ++ sep
     ++ "listings: " ++ show state.(listings) ++ sep
     ++ "purchases: " ++ show state.(purchases) ++ sep
     ++ "timeout: " ++ show state.(timeout)
     ++ "}"
}.

Instance showSerializedMsg : Show SerializedValue :=
  Derive Show Msg < Msg, Setup >.
  

