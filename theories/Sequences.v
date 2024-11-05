Require Import Basics Types.
Require Import Truncations.Core.
Require Import Spaces.Nat.Core.

Open Scope nat_scope.
Open Scope type_scope.

(** A uniform structure on a type consists of an equivalence relation for every natural number, each one being stronger than its predecessor. *)
Class UStructure (us_type : Type) := {
  us_rel : nat -> Relation us_type ;
  us_reflexive : forall n : nat, Reflexive (us_rel n) ;
  us_symmetric : forall n : nat, Symmetric (us_rel n) ; 
  us_transitive : forall n : nat, Transitive (us_rel n) ;
  us_pred : forall (n : nat) (x y : us_type), us_rel n.+1 x y -> us_rel n x y
}.

Notation "u =[ n ] v" := (us_rel n u v) (at level 70).

Definition refl_test (X : Type) (Struct : UStructure X) (n : nat)
  : forall (x y : X), x = y -> us_rel n x y
  := fun x y h => (h # (us_reflexive n x)).  

(** Every type admits the trivial uniform structure with the standard identity type on every level. *)
Global Instance trivial_us {X : Type} : UStructure X.
Proof.
  srapply (Build_UStructure _ (fun n x y => (x = y))).
  exact (fun _ _ _ => idmap).
Defined.

(** The first term of a sequence. *)
Definition head {X : Type} (u : nat -> X) : X := u 0.

(** Shift of a sequence by 1 to the left. *)
Definition tail {X : Type} (u : nat -> X) : (nat -> X) := u o S.

(** Add an term to the start of a sequence. *)
Definition cons {X : Type} : X -> (nat -> X) -> (nat -> X).
Proof.
  intros x u [|n].
  - exact x.
  - exact (u n).
Defined.  

Definition cons_head_tail {X : Type} (u : nat -> X) : cons (head u) (tail u) == u.
Proof.
  by intros [|n].
Defined.  

Definition tail_cons {X : Type} (u : nat -> X) {x : X} : tail (cons x u) == u
  := fun _ => idpath.

(** A uniform structure on types of sequences, with the relation for [n : nat] given by: *)

Definition seq_agree_on {X : Type} (n : nat) : (nat -> X) -> (nat -> X) -> Type.
Proof.
  induction n.
  - intros u v; exact Unit.
  - intros u v; exact ((head u = head v) * (IHn (tail u) (tail v))).
Defined.

Definition seq_agree_homotopic {X : Type} {n : nat} 
  : forall u v : nat -> X, forall h : u == v, seq_agree_on n u v.
(* jdc: better to move args to left of colon *)
Proof.
  induction n.
  - reflexivity. (* jdc: this is an odd tactic to use; you really want [fun _ _ _ => tt], don't you? *)
  - intros u v h.
    constructor. (* jdc: split is a common idiom to use here *)
    + exact (h 0).
    + exact (IHn _ _ (fun n => h n.+1)). 
Defined.

Global Instance us_sequence_type {X : Type} : UStructure (nat -> X).
Proof.
  snrapply Build_UStructure.
  - exact seq_agree_on.
  - intros n u ; apply (seq_agree_homotopic).
    reflexivity.
  - induction n.
    + exact (fun _ _ _ => tt).
    + exact (fun _ _ h => ((fst h)^, IHn _ _ (snd h))).
  - induction n.
    + exact (fun _ _ _ _ _ => tt).
    + exact (fun _ _ _ huv hvw => 
               ((fst huv) @ (fst hvw), IHn _ _ _ (snd huv) (snd hvw))).
  - induction n.  
    + exact (fun _ _ _ => tt).
    + exact (fun _ _ h => (fst h, IHn _ _ (snd h))).
Defined.

(** Definition of a continuous function depending on two uniform structures. *)
Definition is_continuous 
  {X Y : Type} {usX : UStructure X} {usY : UStructure Y} (p : X -> Y)
  := forall (u : X) (m : nat), 
      exists n : nat, 
        forall v : X, (u =[n] v) -> p u =[m] p v.

(** Uniform continuity is temporarily only defined with one uniform structure to not break the CompactTypes file. *)
Definition is_modulus_of_uniform_continuity 
  {X Y : Type} {usX : UStructure X} (n : nat) (p : X -> Y)
  := forall u v : X, u =[n] v -> p u = p v.

Definition is_uniformly_continuous {X Y : Type} {usX : UStructure X} (p : X -> Y)
  := exists n : nat, is_modulus_of_uniform_continuity n p.

Definition is_uniformly_continuous_is_continuous {X Y : Type} {usX : UStructure X} (p : X -> Y) 
  : is_uniformly_continuous p -> is_continuous p
  := fun uc u m => (uc.1 ; fun v => uc.2 u v).

(** A uniformly continuous function takes homotopic sequences to equal outputs. *)
Definition uniformly_continuous_extensionality
  {X Y : Type} (p : (nat -> X) -> Y) (u v : nat -> X) (hp : is_uniformly_continuous p)
  : u == v -> p u = p v
(* jdc: again, (h : u == v) should be to the left of the colon; I won't mention this elsewhere *)
  := fun h => (hp.2 u v (seq_agree_homotopic u v h)).

Definition cons_decreases_modulus {X Y : Type} (p : (nat -> X) -> Y) (n : nat) (b : X)
  : is_modulus_of_uniform_continuity n.+1 p 
    -> is_modulus_of_uniform_continuity n (p o cons b).
Proof.
  intros hSn u v huv.
  apply hSn.
  constructor. (* jdc: maybe these last three lines should be a lemma about =[n] and cons? *)
  - reflexivity.
  - exact huv.
Defined.
