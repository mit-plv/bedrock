(** printing [| $\lceil$ *)
(** printing |] $\rceil$ *)
(** printing ^+ $\hat{+}$ *)

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
