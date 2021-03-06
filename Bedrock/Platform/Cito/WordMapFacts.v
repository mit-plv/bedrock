Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.WordKey.
Module K := W_as_UDT.
Require Import Bedrock.Platform.Cito.WordMap.
Module M := WordMap.
Require Import Coq.FSets.FMapFacts.
Include (Properties M).
Include (Facts M).
Require Import Bedrock.Platform.Cito.FMapFacts1.
Module bug_4066_workaround_1 := WFacts_fun K M.
Include bug_4066_workaround_1.
Module bug_4066_workaround_2 := UWFacts_fun K M.
Include bug_4066_workaround_2.
Require Import Bedrock.Platform.Cito.FMapFacts2.
Module bug_4066_workaround_3 := UWFacts_fun K M.
Include bug_4066_workaround_3.
