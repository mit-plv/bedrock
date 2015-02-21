Set Implicit Arguments.

Require Import LabelMap.
Require Import Equalities.
Module K := Make_UDT LabelKey.
Module M := LabelMap.
Require Import FMapFacts.
Include (Properties M).
Include (Facts M).
Require Import FMapFacts1.
Include (WFacts_fun K M).
Include (UWFacts_fun K M).
Require Import FMapFacts2.
Include (UWFacts_fun K M).