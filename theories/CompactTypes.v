Require Import Basics Types.
Require Import Truncations.Core.
Require Import Spaces.Nat.Core.
Require Import Spaces.Cantor.
Require Import NatSeq.
Require Import Modalities.ReflectiveSubuniverse.
Require Import Truncations.Connectedness.
Require Import Homotopy.Suspension.
Require Import Pointed.
Require Import Universes.TruncType Universes.HSet.

Open Scope nat_scope.
Open Scope pointed_scope.

(*** Want to prove:
- Syspension of any type is compact (could be not pointed, not empty).
- LEM => every type is compact, every pointed type is searchable.
    Is every type not not compact?
- (Conjecture) If the 0-trunc has a section, X is compact <=> ||X||_0 is compact.
- What happens when ||X||_0 has decidable equality.
- Everything is compact <=> LEM for all types
- LEM for Π_{} {a : A & p a = false} => is_compact A.
    (so : is_compact is stronger than LEM for a given type).
- Every HProp is compact => LEM for HProps.
- HProp is compact + the relevant lemmas.
- Compact is closed under retracts. *)

(** Naming conventions following the Agda code by Martin Escardo. We are working with decidable predicates, equivalently functions to Bool. *)

(** One notion of compactness: for every predicate we can decide whether it is always true or not. *)
Definition is_compact (A : Type) : Type
  := (forall p : A -> Bool, {a : A & p a = false} + (forall a : A, p a = true)).

Definition IsDecidable_is_compact {A : Type} (c : is_compact A) : Decidable A.
Proof.
  induction (c (fun (_ : A) => false)) as [c1|c2].
  - exact (inl c1.1).
  - exact (inr (fun a => false_ne_true (c2 a))).
Defined.

Definition is_sig_compact (A : Type) : Type
  := forall P : A -> Type, (forall a : A, Decidable (P a)) -> Decidable (sig P).

Definition pred_Bool {A : Type} (p : A -> Bool) : A -> Type
  := fun a => p a = false.

(** Simplify with the is_true map from TruncType.v *)
Definition pred_Bool_inv {A : Type} (P : A -> Type)
  (dec : forall a : A, Decidable (P a))
  : A -> Bool.
Proof.
  intro a.
  destruct (dec a).
  - exact false.
  - exact true.
Defined.

Definition pred_Bool_inv_eval {A : Type} (P : A -> Type)
  (dec : forall a : A, Decidable (P a)) (a : A) (k : ~ P a)
  : pred_Bool_inv P dec a = true.
Proof.
  unfold pred_Bool_inv.
  destruct (dec a).
  - contradiction (k p).
  - reflexivity.
Defined.

Definition pred_Bool_inv_prop {A : Type} (P : A -> Type)
  (dec : forall a : A, Decidable (P a))
  (a : A) (h : pred_Bool_inv P dec a = false)
  : P a.
Proof.
  destruct (dec a) as [y|n].
  - exact y.
  - apply Empty_rect.
    set (r := pred_Bool_inv_eval P dec a n).
    exact (true_ne_false (r^ @ h)).
Defined.

Definition pred_Bool_inv_eval' {A : Type} (P : A -> Type)
  (dec : forall a : A, Decidable (P a)) (a : A) (k : P a)
  : pred_Bool_inv P dec a = false.
Proof.
  unfold pred_Bool_inv.
  destruct (dec a).
  - reflexivity.
  - contradiction (n k).
Defined.

Definition pred_Bool_inv_prop' {A : Type} (P : A -> Type)
  (dec : forall a : A, Decidable (P a))
  (a : A) (h : pred_Bool_inv P dec a = true)
  : ~ (P a).
Proof.
  destruct (dec a) as [y|n].
  - apply Empty_rect.
    set (r := pred_Bool_inv_eval' P dec a y).
    exact (false_ne_true (r^ @ h)).
  - exact n.
Defined.

Definition is_decidable_pred_Bool {A : Type} (p : A -> Bool)
  : forall a : A, Decidable (pred_Bool p a).
Proof.
  intro a.
  remember (p a) as a0 eqn:r ; induction a0.
  - exact (inr (fun h => (false_ne_true (h^ @ r)))).
  - exact (inl r).
Defined.

Definition is_sig_compact_is_compact {A : Type} (c : is_compact A) : is_sig_compact A.
Proof.
  intros P dec.
  destruct (c (pred_Bool_inv P dec)) as [l|r].
  - exact (inl (l.1; pred_Bool_inv_prop _ _ l.1 l.2)).
  - exact (inr (fun dec' => (pred_Bool_inv_prop' _ _ _ (r dec'.1) dec'.2))).
Defined.

Definition is_compact_is_sig_compact {A : Type} (c : is_sig_compact A) : is_compact A.
Proof.
  intros p.
  destruct (c (pred_Bool p) (is_decidable_pred_Bool p)) as [l|r].
  - exact (inl l).
  - right.
    intro a.
    apply (@negb_ne (p a) false).
    exact (fun w => r (a; w)).
Defined.

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

Definition is_searchable_is_compact_inhabited {A : Type}
  : is_compact A -> A -> is_searchable A.
Proof.
  intros w a p.
  induction (w p) as [l|r].
  - exists l.1.
    intro h; contradiction (false_ne_true (l.2^ @ h)).
  - exists a.
    exact (fun a => r).
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

Definition is_searchable_iff {A : Type} : is_searchable A <-> A * (is_compact A)
  := (fun s => (is_inhabited_is_searchable s, is_compact_is_searchable s),
        fun c => is_searchable_is_compact_inhabited (snd c) (fst c)).

Definition is_compact_Empty : is_compact Empty
  := fun p => (inr (fun a => Empty_rect (fun b => p b = true) a)).

Definition is_compact_Empty' {A : Type} (not : ~A) : is_compact A
  := fun p => ((inr (fun a => Empty_rect (fun _ => p a = true) (not a)))).

Definition compact_iff_searchable_or_empty {A : Type} :
  is_compact A <-> (~ A) + is_searchable A.
Proof.
  constructor.
  - intro h.
    destruct (IsDecidable_is_compact h) as [l|r].
    + exact (inr (is_searchable_is_compact_inhabited h l)).
    + exact (inl (r)).
  - intros [l|r].
    + exact (is_compact_Empty' l).
    + exact (is_compact_is_searchable r).
Defined.

(** Every connected pointed type is searchable. *)
Definition is_searchable_is_connected `{Univalence} (A : pType)
  (c : IsConnected (0 : trunc_index) A)
  : is_searchable A.
Proof.
  intro p.
  exact (pt; fun h => conn_point_elim (-1) _ h).
Defined.

(* Needs additional assumption. *)
Definition is_compact_set_trunc_is_compact `{Univalence} {A : Type} 
  (f : (Tr 0 A) -> A) (sect : forall a, (tr o f) a = a)
  : is_compact A <-> is_compact (Tr 0 A).
Proof.
  constructor.
  - intros cpt p.
    destruct (cpt (p o tr)) as [l|r].
    + exact (inl (tr l.1; l.2)).
    + exact (inr (fun a => (ap p (sect a))^ @ r (f a))).
  - intros cpt p.
    pose (p' := @Trunc_rec 0 A Bool _ p).
    destruct (cpt p') as [l|r].
    + left.
      (* exists (f l.1).
      unfold p' in l.
      pose (s := l.2); simpl in s.
      specialize (sect l.1); simpl in sect. *)
      destruct (cpt (p o f)) as [y|z].
      * exact (f y.1; y.2).
      * unfold p' in l.
        specialize (z l.1).
        admit.
    + (* I assume there is a lemma for this. *)
      exact (inr (fun a => r (tr a))).
    (* pose (p' := p o f).
    destruct (cpt p') as [l|r].
    + exact (inl (f l.1; l.2)).
    + right.
      intro a.
      unfold p' in r.
      specialize (r (tr a)).      *)
Admitted.

Definition is_compact_is_compact_set_trunc {A : Type} (cpt : is_compact (Tr 0 A))
  (f : (Tr 0 A) -> A)
  : is_compact A.
Proof.
  intro p.
  (* pose (p' := @Trunc_rec 0 A Bool _ p). *)
  pose (p' := p o f).
  destruct (cpt p').
  - left.
    destruct s.
    exists (f proj1).
    exact proj2.
  - right.
    intro a.

Admitted.

Definition is_searchable_suspension `{Univalence} (A : Type)
  : is_searchable (Susp A).
Proof.
  intro p.
  remember (p North) as pn eqn:r; induction pn.
  - exists South.
    intro s.
    apply (Susp_ind _ r s).
    intro x.
    apply hset_path2.
  - exists North.
    intro h; contradiction (true_ne_false (h^ @ r)).
Defined.

(* Following https://www.cs.bham.ac.uk/~txw467/tychonoff/InfiniteSearch1.html *)

Definition is_searchable' (A : Type) : Type
  := forall P : A -> Type,
      (forall a : A, Decidable (P a))
        -> exists x : A, ((exists a : A, P a) -> P x).

Definition is_searchable_is_searchable' {A : Type}
  (h : is_searchable' A)
  : is_searchable A.
Proof.
  apply (@is_searchable_iff A); constructor.
  - exact (h (fun _ => Unit) (fun _ => inl tt)).1.
  - apply is_compact_is_sig_compact.
    intros P dec.
    specialize (h P dec).
    destruct (dec h.1) as [l|r].
    + exact (inl (h.1; l)).
    + exact (inr (fun b => (r (h.2 (b.1; b.2))))).
Defined.

Definition is_searchable_is_searchable'2 {A : Type}
  (h : is_searchable' A)
  : is_searchable A.
Proof.
  intro p.
  specialize (h (pred_Bool p) (is_decidable_pred_Bool p)).
  exists h.1.
  intros r a.
  apply (@negb_ne (p a) false).
  intro j.
  specialize (h.2 (a; j)).
  exact (fun h' => true_ne_false (r^ @ h')).
Defined.

Definition is_searchable'_is_searchable {A : Type}
  (h : is_searchable A)
  : is_searchable' A.
Proof.
  apply (@is_searchable_iff A) in h as [a h].
  apply (is_sig_compact_is_compact) in h.
  intros P dec.
  destruct (h P dec) as [l|r].
  - exact (l.1; fun _ => l.2).
  - exact (a; fun h' => Empty_rect (fun _ => P a) (r h')).
Defined.

Definition is_searchable'_is_searchable2 {A : Type}
  (h : is_searchable A)
  : is_searchable' A.
Proof.
  intros P dec.
  set (p := pred_Bool_inv P dec).
  specialize (h p).
  exists h.1.
  intros (a, u).
  remember (p h.1) as b eqn:s; destruct b.
  - specialize (h.2 s a).
    intro w.
    contradiction (true_ne_false (w^ @ ((pred_Bool_inv_eval' P dec a u)))).
  - exact (pred_Bool_inv_prop P dec h.1 s).
Defined.

Definition is_sig_compact_prop (A : Type) : Type
  := forall P : A -> Type,
      (forall a : A, IsHProp (P a))
        -> (forall a : A, Decidable (P a))
          -> Decidable (sig P).

Definition is_sig_compact_prop_is_sig_compact {A : Type}
  (h : is_sig_compact A)
  : is_sig_compact_prop A
  := fun P hP1 hP2 => h P hP2.

Definition predicate_prop_trunction {A : Type} (P : A -> Type)
  := fun a => Trunc (-1) (P a).

(** Next two proofs can definitely be shortened. 
- Use : Decidable(X) -> ~~-stable(X) -> X <-> ||X||_-1. *)
Definition Decidable_predicate_prop_truncation {A : Type} {P : A -> Type}
  (dec : forall a : A, Decidable (P a))
  : forall a : A, Decidable (predicate_prop_trunction P a).
Proof.
  intro a.
  destruct (dec a) as [l|r].
  - exact (inl (tr l)).
  - right.
    intro x.
    strip_truncations.
    exact (r x).
Defined.

Definition sigma_iff_prop_truncation_Decidable {A : Type} {P : A -> Type}
  (dec : forall a : A, Decidable (P a))
  : {x : A & Tr (-1) (P x)} -> {x : A & P x}.
Proof.
  - intros [x hx].
    exact (x; (fst (@merely_inhabited_iff_inhabited_stable (P x) _)) hx).
Defined.

Definition is_sig_compact_sig_compact_prop {A : Type}
  (h : is_sig_compact_prop A)
  : is_sig_compact A.
Proof.
  intros P hP.
  destruct (h (predicate_prop_trunction P)
              _ (Decidable_predicate_prop_truncation hP)) as [[l k]|r].
  - exact (inl (sigma_iff_prop_truncation_Decidable hP (l; k))).
  - right.
    intros [x z].
    exact (r (x; tr z)).
Defined.

Definition is_selection {A : Type} (eps : (A -> Bool) -> A) : Type
  := forall p : A -> Bool, p (eps p) = true -> forall a : A, p a = true.

(** A reformulation of the definition, presenting the witnesses as a selection function. *)

(* Definition is_searchable' (A : Type) : Type
  := {eps : (A -> Bool) -> A & is_selection eps}.

Definition equiv_searchable_searchable'  {A : Type}
  : is_searchable' A <~> is_searchable A
  := equiv_sig_coind _ _.

Definition selection_is_searchable' {A : Type} (cpt' : is_searchable' A)
  := cpt'.1.

Definition selection_property_is_searchable' {A : Type} (cpt' : is_searchable' A)
  := cpt'.2. *)

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

  Definition eps : (X -> Bool) -> X
    := universal_witness is_searchable_X.

  Definition eps_property
    := witness_universality is_searchable_X.

  (* jdc: Explain "uq". Use something self-explanatory instead? *)
  Definition uq_char : (X -> Bool) -> Bool := fun p => p (eps p).

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
                    p (n.+1 ; is_mod) (cons_head_tail u))^
                  @ (consprop (head u) (x1prop h (head u)) (tail u))).
  Defined.

  Definition has_uniformly_searchable_seq_is_searchable
    : is_uniformly_searchable (nat -> X)
    := fun p cont_p
        => (eps_nat cont_p.1 p; fun r => uq_char_nat_spec_2 p cont_p.2 r).

End Uniform_Search.
