Set Implicit Arguments.

Require Import ADT.

Module Make (Import E : ADT).

  Require Import AutoSep.

  Require Import Semantics.
  Module Import SemanticsMake := Make E.

  Section TopSection.

    Require Import Syntax.
    Require Import SemanticsExpr.
    Require Import WordMap.
    Infix "==" := WordMap.Equal.

    Definition TransitTo spec args heap r heap' :=
      exists triples addr ret,
        args = List.map (@Word _) triples /\
        good_inputs heap (List.map (fun x => (Word x, ADTIn x)) triples) /\
        PreCond spec (List.map (@ADTIn _) triples) /\
        PostCond spec (List.map (fun x => (ADTIn x, ADTOut x)) triples) ret /\
        let heap := fold_left store_out triples heap in
        let t := decide_ret addr ret in
        let ret_w := fst t in
        let ret_a := snd t in
        separated heap ret_w ret_a /\
        heap' == heap_upd_option heap ret_w ret_a /\
        r = ret_w.

    Definition match_ret vs rvar rvalue :=
      match rvar with 
        | Some x => rvalue = sel vs x 
        | None => True
      end.

    Require Import GeneralTactics GeneralTactics2 GeneralTactics3 BedrockTactics.

    Lemma RunsTo_TransitTo : forall r f args env spec v v', let f_w := eval (fst v) f in snd env f_w = Some (Foreign spec) -> RunsTo env (Syntax.Call r f args) v v' -> exists ret, TransitTo spec (List.map (eval (fst v)) args) (snd v) ret (snd v') /\ match_ret (fst v') r ret.
      simpl.
      intros.
      inv_clear H0.
      rewrite H4 in H; discriminate.
      rewrite H4 in H; injection H; intros; subst.
      descend.
      unfold TransitTo.
      descend; eauto.
      unfold match_ret.
      destruct r; simpl in *.
      sel_upd_simpl; eauto.
      eauto.
    Qed.

    Lemma TransitTo_RunsTo : forall r f args env spec v v', let f_w := eval (fst v) f in snd env f_w = Some (Foreign spec) -> forall ret, TransitTo spec (List.map (eval (fst v)) args) (snd v) ret (snd v') -> fst v' = upd_option (fst v) r ret -> RunsTo env (Syntax.Call r f args) v v'.
      simpl.
      intros.
      destruct v; destruct v'; simpl in *.
      unfold TransitTo in *; simpl in *.
      openhyp.
      subst; simpl in *.
      eapply RunsToCallForeign; eauto.
    Qed.

    Definition TransitSafe spec args heap :=
      exists pairs,
        args = List.map fst pairs /\
        good_inputs heap pairs /\
        PreCond spec (List.map snd pairs).

    Lemma TransitSafe_Safe : forall f args env spec v, let f_w := eval (fst v) f in snd env f_w = Some (Foreign spec) -> TransitSafe spec (List.map (eval (fst v)) args) (snd v) -> forall r, Safe env (Syntax.Call r f args) v.
      simpl; intros.
      unfold TransitSafe in *.
      openhyp.
      eapply SafeCallForeign; simpl; eauto.
    Qed.

    Lemma Safe_TransitSafe : forall f args env spec v, let f_w := eval (fst v) f in snd env f_w = Some (Foreign spec) -> forall r, Safe env (Syntax.Call r f args) v -> TransitSafe spec (List.map (eval (fst v)) args) (snd v).
      simpl; intros.
      inv_clear H0.
      rewrite H in H4; discriminate.
      rewrite H in H4; injection H4; intros; subst.
      unfold TransitSafe in *.
      descend; eauto.
    Qed.

  End TopSection.

End Make.