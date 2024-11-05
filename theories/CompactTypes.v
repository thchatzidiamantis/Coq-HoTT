Require Import Basics Types.
Require Import Truncations.Core.
Require Import Spaces.Nat.Core.
Require Import Spaces.Cantor.
Require Import BarInduction.
Require Import Modalities.ReflectiveSubuniverse.
Require Import Truncations.Connectedness.
Require Import Homotopy.Suspension.
Require Import Pointed.
Require Import Sequences.

Open Scope nat_scope.
Open Scope pointed_scope.

(** Naming conventions following the Agda code by Martin Escardo. We are working with decidable predicates, equivalently functions to Bool. *)

(** One notion of compactness: for every predicate we can decide whether it is always true or not. *)
Definition is_compact (A : Type) : Type
  := (forall p : A -> Bool, {a : A & p a = false} + (forall a : A, p a = true)).

(** Second notion of compactness, also called searchability: for every predicate we can find a witness for whether it is always true or not. *)
Definition is_searchable (A : Type) : Type 
  := forall p : A -> Bool, {x : A & p x = true -> forall a : A, p a = true}.

Definition universal_witness {A : Type} : is_searchable A -> (A -> Bool) -> A
  := fun w f => (w f).1.

Definition witness_universality {A : Type} (cpt : is_searchable A) (p : A -> Bool) 
  : p (universal_witness cpt p) = true -> forall a : A, p a = true
  := (cpt p).2.

Definition is_searchable_Bool : is_searchable Bool. 
Proof.
  intro p.
  exists (p false).
  intro r.
  remember (p false) as b eqn:s; induction b.
  - destruct a; assumption.
  - contradiction (false_ne_true (s^ @ r)). 
Defined.

(** We prove that a type is searchable if and only if it is compact and inhabited. *)

(* jdc: name?  Maybe embed in next result? *)
Definition test_function (A : Type) (a : A) (p : A -> Bool)
  : (exists x : A , p x = false) + (forall x : A, p x = true) 
    -> {a : A & p a = true -> forall x : A, p x = true}.
Proof. 
  intros [z|z'].
  - exists (z.1).
    intro hz.
    contradiction (false_ne_true (z.2^ @ hz)).
  - exists a.
    exact (fun a => z').
Defined.

Definition is_searchable_is_compact_inhabited {A : Type} : is_compact A -> A -> is_searchable A.
Proof.
  intros w a p.
  exact (test_function A a p (w p)).
Defined.  

Definition is_compact_is_searchable {A : Type} : is_searchable A -> is_compact A.
Proof.
  intros h p.
  remember (p (h p).1) as b eqn:r; induction b.
  - exact (inr ((h p).2 r)).
  - left.
    exists (h p).1; exact r.
Defined.

Definition is_inhabited_is_searchable {A : Type} : is_searchable A -> A
  := fun h => (h (fun a => true)).1.

(** Every connected pointed type is searchable. *)
Definition is_searchable_is_connected `{Univalence} (A : pType) :
  IsConnected (0 : trunc_index) A -> is_searchable A.
Proof.
  intros c p.
  exists pt.
  intro h.
  apply (conn_point_elim (-1) _ h).
Defined.

Definition is_searchable_suspension_ptype `{Univalence} (A : pType)
  : is_searchable (Susp A)
  := is_searchable_is_connected [Susp A , pt] isconnected_susp.

(** A reformulation of the definition, presenting the witnesses as a selection function. *)

Definition is_selection {A : Type} (eps : (A -> Bool) -> A) : Type
  := forall p : A -> Bool, p (eps p) = true -> forall a : A, p a = true.

Definition is_searchable' (A : Type) : Type 
  := {eps : (A -> Bool) -> A & 
      forall p : A -> Bool, p (eps p) = true -> forall a : A, p a = true}.
(* jdc: use is_selection on previous line? *)

(* jdc: This handles some of the things below: *)
Definition shortcut {A : Type} : is_searchable' A <~> is_searchable A
  := equiv_sig_coind _ _.

Definition selection_is_searchable' {A : Type} (cpt' : is_searchable' A) := cpt'.1.

Definition selection_property_is_searchable' {A : Type} (cpt' : is_searchable' A) := cpt'.2.

(*
Check selection_is_searchable'.
Check selection_property_is_searchable'.
*)

Definition is_searchable'_is_searchable {A : Type} (cpt : is_searchable A) 
  : is_searchable' A.
Proof.
  exists (universal_witness cpt).
  exact (witness_universality cpt).
Defined.  

Definition is_searchable_is_searchable' {A : Type} (cpt' : is_searchable' A) 
  : is_searchable A.
Proof.
  intro p.
  exists ((cpt').1 p).
  rapply (cpt').2.
Defined.

(** A type is uniformly searchable if it is searchable over uniformly continuous predicates. *)
Definition is_uniformly_searchable (A : Type) {usA : UStructure A} 
  := forall (p : A -> Bool), 
      is_uniformly_continuous p 
        -> exists w0 : A, (p w0 = true -> forall u : A, p u = true). 

Section Uniform_Search.

  (** Following https://www.cs.bham.ac.uk/~mhe/TypeTopology/TypeTopology.UniformSearch.html, we prove that if [X] is searchable then [nat -> X] is uniformly searchable. *)

  Context {X : Type} (is_searchable_X : is_searchable X).

  (* jdc: this was unused.  But if kept, a Let is better than a Context line:
  Let x0 : X := is_inhabited_is_searchable is_searchable_X. *)

  (* jdc:  I don't understand why we would want this hypothesis.  Maybe it's better to take [c] to be the constant sequence at x0, or something like that?  And maybe better to inline it just to the one use? *)
  Context (c : nat -> X).

  (* jdc: The next two would be more clear using the witness_* functions, I think. *)
  Definition eps : (X -> Bool) -> X := (is_searchable'_is_searchable is_searchable_X).1.

  Definition eps_property := (is_searchable'_is_searchable is_searchable_X).2.
  (* Check eps_property. *)

  (* jdc: Explain "uq". Use something self-explanatory instead? *)
  Definition uq_char : (X -> Bool) -> Bool := fun p => p (eps p).

  (* jdc: not used. *)
  Definition uq_char_spec := fun (p : X -> Bool) 
                              => fun (t : forall x : X, p x = true) => t (eps p).
  (* Check uq_char_spec. *)

  (** The witness function for predicates on [nat -> X] (no uniform continuity required in the construction). *)
  Definition eps_nat (n : nat) : ((nat -> X) -> Bool) -> (nat -> X).
  Proof.
    induction n; intro p.
    - exact c.
    - pose (A q := q (IHn q)).
      pose (y0 := eps (fun x => A (fun a => p (cons x a)))).
      exact (cons y0 (IHn (p o cons y0))).
  Defined.

  Definition uq_char_nat (n : nat) := fun p => p (eps_nat n p).

  (* jdc: not used. *)
  Definition uq_char_nat_spec_1 (p : (nat -> X) -> Bool) (n : nat)
    (is_mod_n : is_modulus_of_uniform_continuity n p)
    (h : forall u : nat -> X, p u = true)
    : uq_char_nat n p = true.
  Proof.
    apply h.
  Defined.

  (** The desired property of the witness function. *)
  Definition uq_char_nat_spec_2 {n : nat} (p : (nat -> X) -> Bool)
    (is_mod : is_modulus_of_uniform_continuity n p)
    (h : uq_char_nat n p = true )
    : forall u : nat -> X, p u = true.
  Proof.
    induction n in p, is_mod, h |- *.
    - exact (fun u => (is_mod u c tt) @ h).
    - intro u. 
      set (x1 := eps (fun y => uq_char_nat n (p o (cons y)))).
      (* jdc: Maybe some parts here should be lemmas?  I didn't look closely. *)
      assert (consprop : forall x : X, 
                      uq_char_nat n (p o (cons x)) = true 
                        -> forall v : nat -> X, p (cons x v) = true).
      + exact (fun _ k => IHn (p o (cons _)) (cons_decreases_modulus p n _ is_mod) k).
      + assert (x1prop : uq_char_nat n (p o (cons x1)) = true 
                          -> forall x : X, uq_char_nat n (p o (cons x)) = true).  
        * exact (fun l x => eps_property (fun y => uq_char_nat n (p o (cons y))) l x).
        * exact ((uniformly_continuous_extensionality 
                    p _ _ (n.+1 ; is_mod) (cons_head_tail u))^ 
                  @ (consprop (head u) (x1prop h (head u)) (tail u))).
  Defined.  

  Definition has_uniformly_searchable_seq_is_searchable : is_uniformly_searchable (nat -> X).
  Proof.
    intros p cont_p.
    exact (eps_nat cont_p.1 p ; fun r => uq_char_nat_spec_2 p cont_p.2 r).
  Defined.

End Uniform_Search.
