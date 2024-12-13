Require Import Basics Types.
Require Import Truncations.Core Truncations.Connectedness.
Require Import Spaces.Nat.Core.
Require Import NatSeq.
Require Import Homotopy.Suspension.
Require Import Pointed.
Require Import Universes.TruncType Universes.HSet.
Require Import Idempotents.

Open Scope nat_scope.
Open Scope pointed_scope.

(** One notion of compactness: for every predicate we can decide whether it is always true or not. *)
Definition compact (A : Type) : Type
  := (forall p : A -> Bool, {a : A & p a = false} + (forall a : A, p a = true)).

(** Any compact type is decidable. *)
Definition decidable_compact {A : Type} (c : compact A) : Decidable A.
Proof.
  induction (c (fun (_ : A) => false)) as [c1|c2].
  - exact (inl c1.1).
  - exact (inr (fun a => false_ne_true (c2 a))).
Defined.

(** Equivalent definition of compactness: If a family over the type is decidable, then the Σ-type is decidable. *)
Definition sig_compact (A : Type) : Type
  := forall P : A -> Type, (forall a : A, Decidable (P a)) -> Decidable (sig P).

(** Maps for moving between the definitions. *)

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
  - contradiction (true_ne_false ((pred_Bool_inv_eval P dec a n)^ @ h)).
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
  - exact (Empty_rec (false_ne_true ((pred_Bool_inv_eval' P dec a y)^ @ h))).
  - exact n.
Defined.

Definition decidable_pred_Bool {A : Type} (p : A -> Bool)
  : forall a : A, Decidable (pred_Bool p a).
Proof.
  intro a.
  remember (p a) as a0 eqn:r ; induction a0.
  - exact (inr (fun h => (false_ne_true (h^ @ r)))).
  - exact (inl r).
Defined.

Definition sig_compact_compact {A : Type} (c : compact A)
  : sig_compact A.
Proof.
  intros P dec.
  destruct (c (pred_Bool_inv P dec)) as [l|r].
  - exact (inl (l.1; pred_Bool_inv_prop _ _ l.1 l.2)).
  - exact (inr (fun dec' => (pred_Bool_inv_prop' _ _ _ (r dec'.1) dec'.2))).
Defined.

Definition compact_sig_compact {A : Type} (c : sig_compact A)
  : compact A.
Proof.
  intros p.
  destruct (c (pred_Bool p) (decidable_pred_Bool p)) as [l|r].
  - exact (inl l).
  - right.
    intro a.
    apply (@negb_ne (p a) false).
    exact (fun w => r (a; w)).
Defined.

(** A weaker definition: for any decidable family, the dependent function type is decidable. *)
Definition pi_compact (A : Type)
  := forall (P : A -> Type) (dec : forall a : A, Decidable (P a)),
      Decidable (forall a : A, P a).

Definition pi_compact_sig_compact {A : Type} (c : sig_compact A)
  : pi_compact A.
Proof.
  intros P dec.
  destruct (c (fun a => ~(P a)) _) as [l|r].
  - right; exact (fun f => l.2 (f l.1)).
  - left.
    intro a.
    apply (stable_decidable (P a)).
    exact (fun u => r (a; u)).
Defined.

(** Second notion of compactness, also called searchability: for every predicate we can find a witness for whether it is always true or not. *)
Definition searchable (A : Type) : Type
  := forall p : A -> Bool, {x : A & p x = true -> forall a : A, p a = true}.

Definition universal_witness {A : Type} : searchable A -> (A -> Bool) -> A
  := fun w f => (w f).1.

Definition witness_universality {A : Type} (s : searchable A) (p : A -> Bool)
  : p (universal_witness s p) = true -> forall a : A, p a = true
  := (s p).2.

Definition searchable_Bool : searchable Bool.
Proof.
  intro p.
  exists (p false).
  intro r.
  remember (p false) as b eqn:s; induction b.
  - destruct a; assumption.
  - contradiction (false_ne_true (s^ @ r)).
Defined.

(** We prove that a type is searchable if and only if it is compact and inhabited. *)

Definition searchable_compact_inhabited {A : Type}
  : compact A -> A -> searchable A.
Proof.
  intros w a p.
  induction (w p) as [l|r].
  - exists l.1.
    intro h; contradiction (false_ne_true (l.2^ @ h)).
  - exists a.
    exact (fun a => r).
Defined.

Definition compact_searchable {A : Type} : searchable A -> compact A.
Proof.
  intros h p.
  remember (p (h p).1) as b eqn:r; induction b.
  - exact (inr ((h p).2 r)).
  - left.
    exists (h p).1; exact r.
Defined.

Definition inhabited_searchable {A : Type} : searchable A -> A
  := fun h => (h (fun a => true)).1.

Definition searchable_iff {A : Type} : searchable A <-> A * (compact A)
  := (fun s => (inhabited_searchable s, compact_searchable s),
        fun c => searchable_compact_inhabited (snd c) (fst c)).

Definition compact_Empty : compact Empty
  := fun p => (inr (fun a => Empty_rec a)).

Definition compact_Empty' {A : Type} (not : ~A) : compact A
  := fun p => ((inr (fun a => Empty_rec (not a)))).

Definition compact_iff_not_or_searchable {A : Type} :
  compact A <-> (~ A) + searchable A.
Proof.
  constructor.
  - intro h.
    destruct (decidable_compact h) as [l|r].
    + exact (inr (searchable_compact_inhabited h l)).
    + exact (inl (r)).
  - intros [l|r].
    + exact (compact_Empty' l).
    + exact (compact_searchable r).
Defined.

(** Every connected pointed type is searchable. *)
Definition searchable_is_connected_pType `{Univalence} (A : pType)
  (c : IsConnected (0 : trunc_index) A)
  : searchable A
  := fun p => (pt; fun h => conn_point_elim (-1) _ h).

(** Compact types are closed under retracts. *)
Definition compact_retract {A : Type} (R : RetractOf A) (c : compact A)
  : compact (retract_type R).
Proof.
  intro p. destruct (c (p o (retract_retr R))) as [l|r].
  + exact (inl ((retract_retr R) l.1; l.2)).
  + exact (inr (fun a => (ap p ((retract_issect R) a))^ @ r ((retract_sect R) a))).
Defined.

Definition compact_retract' {A R : Type} {f : A -> R} {g : R -> A}
  (s : forall a, (f o g) a = a) (c : compact A)
  : compact R.
Proof.
  intro p. destruct (c (p o f)) as [l|r].
  + exact (inl (f l.1; l.2)).
  + exact (inr (fun a => (ap p (s a))^ @ r (g a))).
Defined.

(** Assuming the set truncation map has a section, a type is compact if and only if its set truncation is compact. *)
Definition compact_set_trunc_compact `{Univalence} {A : Type} {n : nat}
  (f : (Tr 0 A) -> A) (s : forall a, (tr o f) a = a)
  : compact A <-> compact (Tr 0 A).
Proof.
  constructor.
  1: exact (compact_retract' s).
  intros cpt p.
  destruct (cpt (Trunc_rec p)) as [l|r].
  - exact (inl (f l.1; ap (Trunc_rec p) (s l.1) @ l.2)).
  - exact (inr (fun a => r (tr a))).
Defined.

(** Could also be done with a map Bool -> Susp A. *)
Definition searchable_suspension `{Univalence} (A : Type)
  : searchable (Susp A).
Proof.
  intro p.
  remember (p North) as pn eqn:r; induction pn.
  - exists South.
    intro hs; apply (Susp_ind _ r hs).
    intro x; apply hset_path2.
  - exists North.
    intro h; contradiction (true_ne_false (h^ @ r)).
Defined.

(* Following https://www.cs.bham.ac.uk/~txw467/tychonoff/InfiniteSearch1.html *)

Definition searchable' (A : Type) : Type
  := forall P : A -> Type,
      (forall a : A, Decidable (P a))
        -> exists x : A, ((exists a : A, P a) -> P x).

Definition searchable_searchable' {A : Type}
  (h : searchable' A)
  : searchable A.
Proof.
  apply (@searchable_iff A); constructor.
  - exact (h (fun _ => Unit) (fun _ => inl tt)).1.
  - apply compact_sig_compact.
    intros P dec.
    specialize (h P dec).
    destruct (dec h.1) as [l|r].
    + exact (inl (h.1; l)).
    + exact (inr (fun b => (r (h.2 (b.1; b.2))))).
Defined.

Definition searchable'_searchable {A : Type}
  (h : searchable A)
  : searchable' A.
Proof.
  apply (@searchable_iff A) in h as [a h].
  apply (sig_compact_compact) in h.
  intros P dec.
  destruct (h P dec) as [l|r].
  - exact (l.1; fun _ => l.2).
  - exact (a; fun h' => Empty_rect (fun _ => P a) (r h')).
Defined.

(** Another equivalent definition of compactness, where we restrict to decidable propositions. *)
Definition sig_compact_prop (A : Type) : Type
  := forall P : A -> HProp,
      (forall a : A, Decidable (P a)) -> Decidable (sig P).

Definition sig_compact_prop_sig_compact {A : Type}
  (h : sig_compact A)
  : sig_compact_prop A
  := fun P hP => h P hP.

Definition predicate_prop_trunction {A : Type} (P : A -> Type)
  : A -> HProp
  := fun a => Build_HProp (Trunc (-1) (P a)).

(** This can definitely be shortened.
- Use : [Decidable(X) -> ~~-stable(X) -> (X <-> (Tr (-1) X))]. *)
Definition decidable_predicate_prop_truncation {A : Type} {P : A -> Type}
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

Definition sig_compact_sig_compact_prop {A : Type}
  (h : sig_compact_prop A)
  : sig_compact A.
Proof.
  intros P hP.
  destruct (h (predicate_prop_trunction P)
              (decidable_predicate_prop_truncation hP)) as [[l k]|r].
  - exact (inl (sigma_iff_prop_truncation_Decidable hP (l; k))).
  - right.
    intros [x z].
    exact (r (x; tr z)).
Defined.

Definition is_selection {A : Type} (eps : (A -> Bool) -> A) : Type
  := forall p : A -> Bool, p (eps p) = true -> forall a : A, p a = true.

(** A type is uniformly searchable if it is searchable over uniformly continuous predicates. *)
Definition uniformly_searchable (A : Type) {usA : UStructure A}
  := forall (p : A -> Bool),
      is_uniformly_continuous p
        -> exists w0 : A, (p w0 = true -> forall u : A, p u = true).

Section Uniform_Search.

  (** Following https://www.cs.bham.ac.uk/~mhe/TypeTopology/TypeTopology.UniformSearch.html, we prove that if [X] is searchable then [nat -> X] is uniformly searchable. *)

  Context {X : Type} (is_searchable_X : searchable X).

  Definition eps : (X -> Bool) -> X
    := universal_witness is_searchable_X.

  Definition eps_property
    := witness_universality is_searchable_X.

  (* uq stands for uniformly continuous, I will change the names here. *)
  Definition uq_char : (X -> Bool) -> Bool := fun p => p (eps p).

  (** The witness function for predicates on [nat -> X] (no uniform continuity required in the construction). *)
  Definition eps_nat (n : nat) : ((nat -> X) -> Bool) -> (nat -> X).
  Proof.
    induction n; intro p.
    - exact (fun _ => inhabited_searchable is_searchable_X).
    - pose (A q := q (IHn q)).
      pose (y0 := eps (fun x => A (fun a => p (cons x a)))).
      exact (cons y0 (IHn (p o cons y0))).
  Defined.

  Definition uq_char_nat (n : nat) := fun p => p (eps_nat n p).

  (** The desired property of the witness function. *)
  Definition uq_char_nat_spec_2 {n : nat} (p : (nat -> X) -> Bool)
    (is_mod : is_modulus_of_uniform_continuity n p)
    (h : uq_char_nat n p = true )
    : forall u : nat -> X, p u = true.
  Proof.
    induction n in p, is_mod, h |- *.
    - exact (fun u =>
            (is_mod u (fun _ => inhabited_searchable is_searchable_X) tt) @ h).
    - intro u.
      pose (x1 := eps (fun y => uq_char_nat n (p o (cons y)))).
      assert (consprop : forall x : X,
                          uq_char_nat n (p o (cons x)) = true
                            -> forall v : nat -> X, p (cons x v) = true).
      + exact (fun _ k =>
                IHn (p o (cons _)) (cons_decreases_modulus p n _ is_mod) k).
      + assert (x1prop : uq_char_nat n (p o (cons x1)) = true
                          -> forall x : X, uq_char_nat n (p o (cons x)) = true).
        * exact (fun l x =>
                  eps_property (fun y => uq_char_nat n (p o (cons y))) l x).
        * exact ((uniformly_continuous_extensionality
                  p (is_u_continuous_has_modulus is_mod) (cons_head_tail u))^
                    @ (consprop (head u) (x1prop h (head u)) (tail u))).
  Defined.

  Definition has_uniformly_searchable_seq_searchable
    : uniformly_searchable (nat -> X)
    := fun p cont_p
        => (eps_nat (cont_p 1).1 p;
            fun r => uq_char_nat_spec_2 p (cont_p 1).2 r).

End Uniform_Search.