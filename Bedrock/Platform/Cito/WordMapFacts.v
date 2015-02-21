Set Implicit Arguments.

Require Import WordKey.
Module K := W_as_UDT.
Require Import WordMap.
Module M := WordMap.
Require Import FMapFacts.
Include (Properties M).
Include (Facts M).
Require Import FMapFacts1.
Include (WFacts_fun K M).
Include (UWFacts_fun K M).
Require Import FMapFacts2.
Include (UWFacts_fun K M).
