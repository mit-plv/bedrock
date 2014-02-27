Set Implicit Arguments.

Require Import GLabelKey.
Module K := GLabel_as_UDT.
Require Import GLabelMap.
Module M := GLabelMap.
Require Import FMapFacts.
Include (Properties M).
Include (Facts M).
Require Import FMapFacts1.
Include (WFacts_fun K M).
Include (UWFacts_fun K M).
Require Import FMapFacts2.
Include (UWFacts_fun K M).
