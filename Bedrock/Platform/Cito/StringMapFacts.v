Set Implicit Arguments.

Require Import StringMap.
Module K := String_as_UDT.
Module M := StringMap.
Require Import FMapFacts.
Include (Properties M).
Include (Facts M).
Require Import FMapFacts1.
Include (WFacts_fun K M).
Include (UWFacts_fun K M).
Require Import FMapFacts2.
Include (UWFacts_fun K M).
