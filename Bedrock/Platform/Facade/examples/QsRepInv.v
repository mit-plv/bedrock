Set Implicit Arguments.

Require Import Bedrock.Platform.AutoSep.
Require Import Bedrock.Platform.Facade.examples.QsADTs.
Import Adt.
Require Import Bedrock.Platform.Cito.RepInv.

Require Import Bedrock.Platform.Facade.examples.ArrayTupleF Bedrock.Platform.Facade.examples.TupleListF Bedrock.Platform.Facade.examples.Tuples0F Bedrock.Platform.Facade.examples.Tuples1F.

Definition rep_inv p adtvalue : HProp :=
  match adtvalue with
    | Tuple t => tuple t p
    | List ts => lseq ts p
    | Tuples0 len ts => tuples0 len ts p
    | Tuples1 len key ts => tuples1 len key ts p
  end.

Module Ri <: RepInv QsADTs.Adt.

  Definition RepInv := W -> ADTValue -> HProp.

  Definition rep_inv := rep_inv.

  Lemma rep_inv_ptr : forall p a, rep_inv p a ===> p =?> 1 * any.
  Proof.
    destruct a; simpl.

    eapply Himp_trans; [ apply tuple_fwd | ].
    sepLemmaLhsOnly.
    fold (@length W) in *.
    Transparent Malloc.freeable.
    unfold Malloc.freeable in H0.
    destruct t; simpl in *; intuition (try omega).
    destruct t; simpl in *; intuition (try omega).
    unfold array; simpl.
    sepLemma; apply any_easy.

    eapply Himp_trans; [ apply lseq_fwd | sepLemma ]; apply any_easy.

    unfold tuples0; sepLemma; apply any_easy.

    eapply Himp_trans; [ apply tuples1_fwd | sepLemma ]; apply any_easy.
  Qed.

End Ri.
