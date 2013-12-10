(** A theory of algebraic datatypes with associated invariants *)

Require Import AutoSep.

Require Import Depl.Logic Depl.Cancel.


(** * Syntax of algebraic datatype definitions *)

(** A datatype's rep. predicate takes as argument a single functional-model value in [dyn]. *)

(** One constructor of a datatype *)
Record con := {
  Recursive : list string;
  (** Names for the "record fields" that actually exist at runtime,
    * referencing other objects of this same datatype.
    * In [Condition] below, these names refer to the _functional_models_ of the recursive arguments.
    * There's no need to refer to their pointer values. *)
  Nonrecursive : list string;
  (** Names of the remaining fields that don't point to further objects of this datatype.
    * These _do_ get bound to machine-word values. *)
  Condition : pred
  (** Finally, the property describing associated memory resources.
    * It does _not_ describe the transitive conditions imposed by other values of the same algebraic
    * datatype that this node points to. *)
}.

Definition datatype := list con.


(** * Semantics of datatypes *)

(** This type summarizes the shape of a datatype value, for purposes of well-founded recursion. *)
Inductive skeleton :=
| Skeleton (sks : list skeleton).

Section Semantics.
  Open Scope Sep_scope.

  (** We'll represent recursive arguments as pairs of models and pointers.
    * Here are some functions to disentangle them. *)
  Definition addrs : list (dyn * W) -> list W := map (@snd _ _).
  Definition models : list (dyn * W) -> list dyn := map (@fst _ _).

  (** Nonrecursive fields are all [W], but we'll want to convert them to [dyn]. *)
  Definition dynify : list W -> list dyn := map (@Dyn _).

  (** Helpers for building first-order variable environments *)
  Fixpoint make_fo (names : list string) (values : list dyn) : fo_env :=
    match names, values with
      | name :: names, valu :: values =>
        fo_set (make_fo names values) name valu
      | _, _ => fo_empty
    end.

  Section children.
    (** Stand-in for the final rep. predicate we define *)
    Variable self : skeleton -> dyn -> W -> HProp.

    (** In the main constructor denotation definition, we will need to iterate over all recursive children,
      * in a way that the termination checker understands.  Here's a helper function for just that. *)
    Fixpoint children (sks : list skeleton) (rs : list (dyn * W)) : HProp :=
      match sks, rs with
        | sk :: sks, r :: rs => self sk (fst r) (snd r) * children sks rs
        | _, _ => Emp
      end.

    Definition conD
      (c : con)             (* Which constructor are we representing? *)
      (tag : W)             (* Which numeric tag has been assigned to it? *)
      (sks : list skeleton) (* Which skeleton goes with this node? *)
      (model : dyn)         (* What functional model was passed to the overall rep. predicate? *)
      (ptr : W)             (* What is the first address used to represent this type? *)
      : HProp :=
      (* There exist values for the recursive and nonrecursive fields... *)
      Ex rs, Ex ns,
        (* Laid out at the appropriate address, we find the tag and arguments. *)
        ptsto32m _ ptr O (tag :: addrs rs ++ ns)
        (* We picked the right number of fields in each category. *)
        * [| length rs = length (Recursive c) |]
        * [| length ns = length (Nonrecursive c) |]
        (* The side condition holds w.r.t. the field values. *)
        * predD (Condition c) (fun _ _ => Emp)
        (make_fo (Recursive c ++ Nonrecursive c) (models rs ++ dynify ns))
        (* Finally, all child nodes are accounted for. *)
        * children sks rs.
  End children.

  (** Let's focus in on one datatype. *)
  Variable dt : datatype.

  (** The final rep. predicate *)
  Fixpoint datatypeD (sk : skeleton) (model : dyn) (ptr : W) : HProp :=
    match sk with
      | Skeleton sks =>
        (** It turned out to be the [n]th constructor, whose definition is [c]... *)
        Ex n, Ex c, [| nth_error dt n = Some c |]
          (* ...and this node is sitting in memory where we expect it. *)
          * conD datatypeD c n sks model ptr
    end.
End Semantics.
