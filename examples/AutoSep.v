Require Import Bedrock.

Set Implicit Arguments.

(** * Let's read from memory! *)

Import SepTac.BedrockEvaluator.
Require Import Bedrock.sep.PtsTo.

Module PLUGIN_PTSTO := BedrockPtsToEvaluator SepTac.PLUGIN.

About PLUGIN_PTSTO.SymEval_ptsto32.

Definition readS : assert := st ~> ExX, Ex v, ![ $0 =*> v * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Rv = v |] /\ ![ $0 =*> v * #1 ] st).

Definition read := bmodule "read" {{
  bfunction "read" [readS] {
    Rv <- $[0];;
    Goto Rp
  }
}}.

Theorem readOk : moduleOk read.
  structured_auto.  ; autorewrite with sepFormula in *; simpl in *.

  unfold ReadWord, mem_get_word, footprint_w, ReadByte in *; auto.
  auto.

  ho. admit. (** TODO: Safety proof **)

  About sym_evalInstrs.
  Implicit Arguments sym_evalInstrs [ types' funcs fPlus fMinus fTimes sfuncs ].

  Definition knowns := 0 :: nil.
  About sym_evalInstrs_apply.

  unfold starB in *.
    match goal with
      | [ H : evalInstrs ?stn ?st ?is = _ 
        , H' : PropX.interp ?cs (SepIL.SepFormula.sepFormula ?SF (?stn, ?st)) |- _ ] =>
        match find_reg st Rp with
          | (?rp_v, ?rp_pf) =>
            match find_reg st Sp with
              | (?sp_v, ?sp_pf) =>
                match find_reg st Rv with
                  | (?rv_v, ?rv_pf) => 
        let regs := constr:((rp_v, (sp_v, (rv_v, tt)))) in
        let Ts := constr:(@nil Type) in
        let Ts := collectTypes_instrs is Ts in
        let Ts := SEP.collectAllTypes_expr isConst Ts regs in
        let Ts := SEP.collectAllTypes_sexpr isConst Ts (SF :: nil) in
        let types := eval unfold bedrock_types in bedrock_types in
        let types := SEP.extend_all_types Ts types in
        match types with
          | _ :: _ :: _ :: ?types_ext =>
            let funcs := eval unfold bedrock_funcs in (bedrock_funcs types_ext) in
            let funcs := eval simpl in funcs in
            let sfuncs := constr:(@nil (@SEP.ssignature types pcT stT)) in
            let uvars := eval simpl in (@nil _ : Expr.env types) in
            let vars := eval simpl in (@nil _ : Expr.env types) in
            reflect_instrs ltac:(isConst) is types funcs uvars vars ltac:(fun funcs sis =>
            SEP.reflect_expr ltac:(isConst) rp_v types funcs uvars vars ltac:(fun funcs rp_v =>
            SEP.reflect_expr ltac:(isConst) sp_v types funcs uvars vars ltac:(fun funcs sp_v =>
            SEP.reflect_expr ltac:(isConst) rv_v types funcs uvars vars ltac:(fun funcs rv_v =>
            SEP.reflect_sexpr ltac:(isConst) SF types funcs pcT stT sfuncs uvars vars ltac:(fun funcs sfuncs SF =>
              idtac "here" H' ;
            generalize (@sym_evalInstrs_apply types_ext funcs (fPlus _) (fMinus _) (fMult _) sfuncs nil DepList.HNil
              (fPlus_correct _ _) (fMinus_correct _ _) (fMult_correct _ _) uvars vars cs is stn st _ H sp_v rv_v rp_v SF H'
              sp_pf rv_pf rp_pf _ (refl_equal _) sis) (* _ (refl_equal _) (refl_equal _)); simpl stateD; intro *) )))))
        end
                end
            end
        end
    end.
    simpl.
    Set Printing Implicit.
    unfold types.

    simpl SEP.sexprD.




  sepRead.
  reflexivity.
Qed.

(** Identity function, using a simple calling convention *)

Definition identityS : assert := st ~> Ex a, ![ st#Sp ==> a ] st /\ st#Rp @@ (st' ~> [| st'#Rv = a /\ st'#Sp = st#Sp |]).
Definition identity := bmodule "identity" {{
  bfunction "identity" [identityS] {
    Rv <- $[Sp];;
    Goto Rp
  }
}}.
Theorem identityOk : moduleOk identity.
  structured; ho. sepRead; reflexivity.
Qed.

(** One-word memory preservation *)
Definition preserveS : assert := st ~> ![ $0 ==> $0 ] st /\ st#Rp @@ (st' ~> ![ $0 ==> $0 ] st').
Definition preserve := bmodule "preserve" {{
  bfunction "preserve" [preserveS] {
    Goto Rp
  }
}}.
Theorem preserveOk : moduleOk preserve.
  structured. ho. autorewrite with sepFormula. assumption.
Qed.

(** Write *)
Definition writeS : assert := st ~> Ex v, ![ $0 ==> v ] st /\ st#Rp @@ (st' ~> ![ $0 ==> $0 ] st').
Definition write := bmodule "write" {{
  bfunction "write" [writeS] {
    $[0] <- 0;;
    Goto Rp
  }
}}.
Theorem writeOk : moduleOk write.
  structured; ho. specialize (H3 (stn, x)). autorewrite with sepFormula in *; eauto.
  rewrite sepFormula_eq in *.
  generalize dependent H0.
  propxFo. unfold WriteWord. 
 info propxFo.
Abort.

(** Unknown memory *)
Definition unknownS : assert := st ~> Ex g0, ![ st#Sp ==> g0 ] st /\ st#Rp @@ (st' ~> Ex g1, ![ st'#Sp ==> g1 ] st' /\ [| st#Sp = st'#Sp |]).
Definition unknown := bmodule "unknown" {{
  bfunction "unknown" [unknownS] {
    Goto Rp
  }
}}.
Theorem unknownOk : moduleOk unknown.
  structured. ho. exists x. autorewrite with sepFormula in *. ho. propxFo. (* simplify_fwd *)
Qed.


(** Constant memory swap function *)
Definition swapS : assert := st ~> Ex pa, Ex pb, Ex a, Ex b, Ex g0, Ex g1, Ex g2, Ex g3,
  ![ st#Sp ==> pa * (st#Sp^+$4) ==> pb * (st#Sp^-$4) ==> g0 * (st#Sp^-$8) ==> g1 * pa ==> a * pb ==> b ] st /\
  st#Rp @@ (st' ~> ![ st#Sp ==> pa * (st#Sp^+$4) ==> pb * (st#Sp^-$4) ==> g2 * (st#Sp^-$8) ==> g3 * pa ==> a * pa ==> b ] st').
Definition swap := bmodule "swap" {{
  bfunction "swap" [swapS] {
    Goto Rp
  }
}}.
Theorem swapOk : moduleOk swap.
Abort.

(** Swap function *)

(* stack grows down, top argument is on bottom. This is mostly forced
by the fact that Indir only takes positive offsets. *)
Definition swapS' : assert := st ~> Ex pa, Ex pb, Ex a, Ex b,
  ![ st#Sp ==> pa * (st#Sp^+$4) ==> pb * pa ==> a * pb ==> b ] st /\
  st#Rp @@ (st' ~> ![ pa ==> b * pb ==> a ] st' ).
Definition swap' := bmodule "swap'" {{
  bfunction "swap'" [swapS'] {
    (* due to huge resource constraints, we need to keep Rv available to load pointer locations *)
    Sp <- Sp - 8;;
    Rv <- $[Sp+$8];;
    $[Sp] <- $[Rv];;
    Rv <- $[Sp+$12];;
    $[Sp+$4] <- $[Rv];;
    $[Rv] <- $[Sp];;
    Rv <- $[Sp+$8];;
    $[Rv] <- $[Sp+$4];;
    Sp <- Sp + 8;;
    Goto Rp
  }
}}.
Theorem swapOk : moduleOk swap.
Abort.

(** * Dirt-simple test cases for implication automation *)
Ltac isConst e :=
  match e with
    | true => true
    | false => true
    | O => true
    | S ?e => isConst e
    | _ => false
  end.

Opaque SEP.himp.

Theorem ptsto_refl : forall a v,
  a ==> v ===> a ==> v.
Proof.
  intros.
  reflect_goal ltac:(isConst) (@nil Expr.type).
  intro. SEP.canceler tt.
  reflexivity.
Qed.

Theorem ptsto_comm : forall a1 v1 a2 v2,
  a1 ==> v1 * a2 ==> v2 ===> a2 ==> v2 * a1 ==> v1.
Proof.
  intros.
  reflect_goal ltac:(isConst) (@nil Expr.type).
  intro. SEP.canceler tt. reflexivity.
Qed.


(** * Linked list ADT *)

Module Type LINKED_LIST.
  Parameter llist : list W -> W -> HProp.

  Axiom llist_nil_fwd : forall ls a, a = 0
    -> llist ls a ===> [| ls = nil |].

  Axiom llist_nil_bwd : forall ls a, a = 0
    -> [| ls = nil |] ===> llist ls a.

  Axiom llist_cons_fwd : forall ls a, a <> $0
    -> llist ls a ===> Ex x, Ex ls', Ex p, [| ls = x :: ls' |] * a ==> x * (a ^+ $4) ==> p * llist ls' p.

  Axiom llist_cons_bwd : forall ls a, a <> $0
    -> (Ex x, Ex ls', Ex p, [| ls = x :: ls' |] * a ==> x * (a ^+ $4) ==> p * llist ls' p) ===> llist ls a.
End LINKED_LIST.

Module LinkedList : LINKED_LIST.
  Open Scope Sep_scope.

  Fixpoint llist (ls : list W) (a : W) : HProp :=
    match ls with
      | nil => [| a = 0 |]
      | x :: ls' => Ex p, a ==> x * (a ^+ $4) ==> p * llist ls' p
    end.

  Theorem llist_nil_fwd : forall ls a, a = 0
    -> llist ls a ===> [| ls = nil |].
  Admitted.

  Theorem llist_nil_bwd : forall ls a, a = 0
    -> [| ls = nil |] ===> llist ls a.
  Admitted.

  Theorem llist_cons_fwd : forall ls a, a <> $0
    -> llist ls a ===> Ex x, Ex ls', Ex p, [| ls = x :: ls' |] * a ==> x * (a ^+ $4) ==> p * llist ls' p.
  Admitted.

  Theorem llist_cons_bwd : forall ls a, a <> $0
    -> (Ex x, Ex ls', Ex p, [| ls = x :: ls' |] * a ==> x * (a ^+ $4) ==> p * llist ls' p) ===> llist ls a.
  Admitted.
End LinkedList.
