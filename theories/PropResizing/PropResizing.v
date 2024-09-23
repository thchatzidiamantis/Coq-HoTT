Require Import Basics.Overture Basics.Tactics Basics.Trunc Basics.Equivalences.

Set Universe Minimization ToSet.

(** * Propositional resizing *)

Local Open Scope path_scope.

(** See the note by [Funext] in Overture.v regarding classes for axioms *)
Monomorphic Axiom PropResizing : Type0.
Existing Class PropResizing.

(** Mark this axiom as a "global axiom", which some of our tactics will automatically handle. *)
Global Instance is_global_axiom_propresizing : IsGlobalAxiom PropResizing := {}.

(** Propositional resizing says that every (-1)-truncated type is small. *)
Axiom issmall_hprop@{i j | } : forall `{PropResizing} (X : Type@{j})
  (T : IsHProp X), IsSmall@{i j} X.
Existing Instance issmall_hprop.

Definition resize_hprop@{i j | } `{PropResizing} (A : Type@{j}) `{IsHProp A}
  : Type@{i}
  := @smalltype@{i j} _ (issmall_hprop@{i j} A _).

Definition equiv_resize_hprop@{i j | } `{PropResizing} (A : Type@{j}) `{IsHProp A}
  : A <~> resize_hprop@{i j} A
  := (equiv_smalltype A)^-1%equiv.

Global Instance ishprop_resize_hprop
       `{PropResizing} (A : Type) `{IsHProp A}
  : IsHProp (resize_hprop A)
  := istrunc_equiv_istrunc A (equiv_resize_hprop A).
