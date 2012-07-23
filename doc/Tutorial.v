(** printing [| $\lceil$ *)
(** printing |] $\rceil$ *)
(** printing ^+ $\hat{+}$ *)
(** printing =*> $\mapsto$ *)
(** printing ==*> $\mapsto$ *)
(** printing Ex $\exists$ *)
(** printing <-* $\leftarrow{}*$ *)
(** printing *<- $*\leftarrow$ *)
(** printing * $*$ *)
(** printing ===> $\Longrightarrow$ *)

(** %\textbf{%#<b>#Bedrock#</b>#%}% is a #<a href="http://coq.inria.fr/">#Coq#</a># library that supports implementation, specification, and verification of low-level programs.  Low-level means roughly %``%#"#at the level of C or assembly,#"#%''% and the idea of %``%#"#systems programming#"#%''% is closely related, as some of the primary target domains for Bedrock are operating systems and runtime systems.

   Bedrock is _foundational_, meaning that one needs to trust very little code to believe that a program has really been verified.  Bedrock supports _higher-order_ programs and specifications.  That is, programs may pass code pointers around as data, and specifications are allowed to quantify over other specifications.  Bedrock supports _mostly automated_ proofs, to save programmers from the tedium of step-by-step formal derivations; and Bedrock is also an _extensible low-level programming language_, where programmers can add new features by justifying their logical soundness.

   This advertising pitch can be a bit of a mouthful.  To make things more concrete, we'll start with three small examples.  Some knowledge of Coq will be helpful in what follows, but especially our first pass through the examples should be accessible to a broad audience with a basic level of %``%#"#POPL literacy.#"#%''%  This document is generated from a literate Coq source file using %\texttt{%#<tt>#coqdoc#</tt>#%}%. *)


(** * Three Verified Bedrock Programs *)

(** ** A Trivial Example: The Addition Function *)

(** To begin, we issue the following magic incantation to turn a normal Coq session into a Bedrock session, where we have run Coq with command-line arguments %\texttt{%#<tt>#-R BEDROCK/src Bedrock -I BEDROCK/examples#</tt>#%}%, with %\texttt{%#<tt>#BEDROCK#</tt>#%}% replaced by the directory for a Bedrock installation, where we have already run %\texttt{%#<tt>#make#</tt>#%}% successfully, at least up through the point where it finishes building %\texttt{%#<tt>#AutoSep.vo#</tt>#%}%. *)

Require Import AutoSep.

(** Importing a library module may not seem like magic, but this module, like any other module in Coq may choose to do, exports syntax extensions and tactics that allow a very different sort of coding than one sees in most Coq developments.  We demonstrate by implementing a function for adding together two machine integers.  Bedrock is an environment for _verified_ programming, so we should start by writing a _specification_ for our function. *)

Definition addS := SPEC("n", "m") reserving 0
  PRE[V] [| True |]
  POST[R] [| R = V "n" ^+ V "m" |].

(** Up through the [:=], this is normal Coq syntax for associating an identifier with a definition.  Past that point, we use a special Bedrock notation.  The [SPEC("n", "m")] part declares this as a spec for a function of two arguments with the given formal parameter names, and [reserving 0] declares that this function will require no more stack space than is needed to store its parameters.  (As Bedrock is targeted at operating systems and similar lowest-level code, we opt for static tracking of stack space usage, rather than forcing use of a fixed dynamic regime for avoiding stack overflows.)

   A specification includes a _precondition_ and a _postcondition_.  The notation [PRE[V]] introduces a precondition, binding a local variable [V] that can be used to refer to the function argument values.  In this example, we impose no conditions on the arguments, so the precondition is merely [True].  Actually, Bedrock uses a fancier domain of logical assertions than Coq's usual [Prop], so we need to use the [[| ... |]] operator to _lift_ a normal proposition as an assertion.  More later on what assertions really are.  %Note that the rendering here uses pretty \LaTeX{} symbols; see some of the files in the \texttt{examples} directory for the concrete ASCII syntax.%

   A postcondition begins with the notation [POST[R]], which introduces a local variable [R] to stand for the function return value.  In our postcondition above, we require that the return value equals the sum of the two function arguments, where we write addition with the [^+] operator, which applies to machine words.

   Now that we know _what_ our function is meant to do, we can show _how_ to do it with an implementation.  This will be a Bedrock _module_, which in general might contain several functions, but which will only contain one function here. *)

Definition addM := bmodule "add" {{
  bfunction "add"("n", "m") [addS]
    Return "n" + "m"
  end
}}.

(** The syntax should be mostly self-explanatory, for readers familiar with the C programming language.  Two points are nonstandard, beyond just the concrete syntax.  First, we refer to variable names with string literals.  These are _not_ string literals in the Bedrock programming language, but merely a trick to get Coq's lexer to accept C-like programs.  Second, the function header ends in a Coq term between square brackets.  This is the position where each function _must_ have a specification.

   It doesn't seem surprising that [addM] should be a correct implementation of an addition function, but, just to be sure, let's _prove it_. *)

Theorem addMOk : moduleOk addM.
Proof.
  vcgen; sep_auto.
Qed.

(** The predicate [moduleOk] captures the usual notion from Hoare Logic, etc., of when a program satisfies a specification.  Here we prove correctness by chaining invocations of two tactics: [vcgen], which performs _verification condition generation_, reducing program correctness to a set of proof obligations that only refer directly to straightline code, not structured code; and [sep_auto], a simplification procedure based on _separation logic_ that is quite a bit of overkill for this example, but gets the job done.  (There actually _is_ some quite non-trivial reasoning going on behind the scenes here, dealing with complexity hidden by our nice notations; more on that later.) *)


(** ** Pointers and Memory: A Swap Function *)

(** A crucial component of low-level programming is mutable state, which we introduce with a simple example: a function that takes two pointers as arguments and swaps the values in the memory cells that they point to.  Here is its spec. *)

Definition swapS := SPEC("x", "y") reserving 2
  Ex v, Ex w,
  PRE[V] V "x" =*> v * V "y" =*> w
  POST[_] V "x" =*> w * V "y" =*> v.

(** We see several important changes from the last spec.  First, this time we reserve 2 stack slots, to use for local variable temporaries.  Second, the spec is _existentially quantified_.  The function may be called whenever the precondition can be satisfied _for some values of [v] and [w]_.  Note that the same quantifier variables appear in precondition and postcondition, giving us a way to connect the initial and final states of a function call.

   Both precondition and postcondition use notation inspired by _separation logic_.  The syntax [p =*> v] indicates that pointer [p] points to a memory cell holding value [v].  The [*] operator combines facts about smaller memories into facts about larger composite memories.  The concrete precondition above says that the function will be aware of only two memory cells, whose addresses come from the values of parameters ["x"] and ["y"].  These cells start out holding [v] and [w], respectively.  The postcondition says that the function swaps these values.

   Here is an implementation. *)

Definition swap := bmodule "swap" {{
  bfunction "swap"("x", "y", "v", "w") [swapS]
    "v" <-* "x";;
    "w" <-* "y";;
    "x" *<- "w";;
    "y" *<- "v";;
    Return 0
  end
}}.

(** We write private local variables as extra function formal parameters.  The operator [;;] sequences commands, the operator [<-*] is a memory read, and [*<-] is memory write.

   Our function is not very complex, but there are still opportunities for mistakes.  A quick verification establishes that we implemented it right after all. *)

Theorem swapOk : moduleOk swap.
Proof.
  vcgen; sep_auto.
Qed.


(** ** An Abstract Predicate: In-Place List Reverse *)

(** Bedrock also supports highly automated verifications that involve _data structures_, formalized in a way along the lines of _abstract predicates_ in separation logic.  As an example, consider the following recursive definition of an abstract predicate for singly linked lists. *)

Fixpoint sll (ls : list W) (p : W) : HProp :=
  match ls with
    | nil => [| p = 0 |]
    | x :: ls' => [| p <> 0 |] * Ex p', (p ==*> x, p') * sll ls' p'
  end%Sep.

(** The type [W] is for machine words, and the [%Sep] at the end of the definition asks to parse the function body using the rules for separation logic-style assertions.

   The predicate [sll ls p] captures the idea that mathematical list [ls] is encoded in memory, starting from root pointer [p].  The codomain [HProp] is the domain of predicates over memories.

   We define [sll] by recursion on the structure of [ls].  If the list is empty, then we merely assert the lifted fact [p = 0], forcing [p] to be null.  Note that a lifted fact takes up no memory, so we implicitly assert emptiness of whatever memory this [HProp] is later applied to.

   If the list is nonempty, we split it into head [x] and tail [ls'].  Next, we assert that [p] is not null, and that there exists some pointer [p'] such that [p] points in memory to the two values [x] and [p'], such that [p'] is the root of a list encoding [ls'].  By using [*], we implicitly require that all of the memory regions that we are describing are _disjoint_ from each other.

   To avoid depending on Coq's usual axiom of functional extensionality, Bedrock requires that we prove administrative lemmas like the following for each new separation logic-style predicate we define. *)

Theorem sll_extensional : forall ls (p : W), HProp_extensional (sll ls p).
Proof.
  destruct ls; reflexivity.
Qed.

(** We add the lemma as a hint, so that appropriate machinery within Bedrock knows about it. *)

Hint Immediate sll_extensional.

(** We want to treat the predicate [sll] abstractly, relying only on a set of rules for simplifying its uses.  For instance, here is an implication in separation logic, establishing the consequences of a list with a null root pointer. *)

Theorem nil_fwd : forall ls (p : W), p = 0
  -> sll ls p ===> [| ls = nil |].
Proof.
  destruct ls; sepLemma.
Qed.

(** The proof only needs to request a case analysis on [ls] and then hand off the rest of the work to [sepLemma], a relative of [sep_auto].  Staying at more or less this same level of automation, we also prove 3 more useful facts about [sll]. *)

Theorem nil_bwd : forall ls (p : W), p = 0
  -> [| ls = nil |] ===> sll ls p.
Proof.
  destruct ls; sepLemma.
Qed.

Theorem cons_fwd : forall ls (p : W), p <> 0
  -> sll ls p ===> Ex x, Ex ls', [| ls = x :: ls' |] * Ex p', (p ==*> x, p') * sll ls' p'.
Proof.
  destruct ls; sepLemma.
Qed.

Theorem cons_bwd : forall ls (p : W), p <> 0
  -> (Ex x, Ex ls', [| ls = x :: ls' |] * Ex p', (p ==*> x, p') * sll ls' p') ===> sll ls p.
Proof.
  destruct ls; sepLemma;
    match goal with
      | [ H : _ :: _ = _ :: _ |- _ ] => injection H; sepLemma
    end.
Qed.

(** So that Bedrock knows to use these rules where applicable, we combine them into a _hint package_, using a Bedrock tactic [prepare]. *)

Definition hints : TacPackage.
  prepare (nil_fwd, cons_fwd) (nil_bwd, cons_bwd).
Defined.

(** Now that we have our general %``%#"#theory of lists#"#%''% in place, we can specify and verify in-placed reversal for lists. *)

Definition revS := SPEC("x") reserving 3
  Ex ls,
  PRE[V] sll ls (V "x")
  POST[R] sll (rev ls) R.

Definition revM := bmodule "rev" {{
  bfunction "rev"("x", "acc", "tmp1", "tmp2") [revS]
    "acc" <- 0;;
    [Ex ls, Ex accLs,
      PRE[V] sll ls (V "x") * sll accLs (V "acc")
      POST[R] sll (rev_append ls accLs) R ]
    While ("x" <> 0) {
      "tmp2" <- "x";;
      "tmp1" <- "x" + 4;;
      "x" <-* "tmp1";;
      "tmp1" *<- "acc";;
      "acc" <- "tmp2"
    };;
    Return "acc"
  end
}}.

(** Note that the function implementation contains a [While] loop with a _loop invariant_ before it.  As for all instances of invariants appearing within Bedrock programs, we put the loop invariant within square brackets.  We must be slightly clever in stating what is essentially a strengthened induction hypothesis.  Where the overall function is specified in terms of the function [rev], reasoning about intermediate loop states requires use of the [rev_append] function.

   Tactics like [sep_auto] take care of most reasoning about programs and memories.  A finished Bedrock proof generally consists of little more than the right hints to finish the rest of the process.  The [hints] package we created above supplies rules for reasoning about memories and abstract predicates, and we can use Coq's normal hint mechanism to help with goals that remain, which will generally be about more standard mathematical domains.  Our example here uses Coq's [list] type family, and the only help Bedrock needs to verify ["rev"] will be a lemma from the standard library that relates [rev] and [rev_append], added to a hint database that Bedrock uses in simplifying separation logic-style formulas. *)

Hint Rewrite <- rev_alt : sepFormula.

(** Now the proof script is almost the same as before, except we call Bedrock tactic [sep] instead of [sep_auto].  The former takes a hint package as argument. *)

Theorem revMOk : moduleOk revM.
Proof.
  vcgen; sep hints.
Qed.
