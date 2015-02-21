Set Implicit Arguments.

Require Import Platform.Cito.GLabelKey.
Module K := GLabel_as_UDT.
Require Import Platform.Cito.GLabelMap.
Module M := GLabelMap.
Require Import Coq.FSets.FMapFacts.
Include (Properties M).
Include (Facts M).
Require Import Platform.Cito.FMapFacts1.
Include (WFacts_fun K M).
Include (UWFacts_fun K M).
Require Import Platform.Cito.FMapFacts2.
Include (UWFacts_fun K M).
