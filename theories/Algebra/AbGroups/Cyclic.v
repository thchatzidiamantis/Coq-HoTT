Require Import Spaces.Nat Spaces.Int WildCat
  AbelianGroup AbHom Centralizer AbGroups.Z AbProjective
  Groups.FreeGroup Groups.Image.

(** * Cyclic groups *)

(** ** The free group on one generator *)

(** We can define the integers as the free group on one generator, which we denote [Z1] below. Results from Centralizer.v and Groups.FreeGroup let us show that [Z1] is abelian. *)

(** We define [Z] as the free group with a single generator. *)
Definition Z1 := FreeGroup Unit.
Definition Z1_gen : Z1 := freegroup_in tt. (* The generator *)

Definition Z1_rec {G : Group} (g : G) : Z1 $-> G
  := FreeGroup_rec _ _ (unit_name g).

(* The free group [Z] on one generator is isomorphic to the subgroup of [Z] generated by the generator.  And such cyclic subgroups are known to be commutative, by [commutative_cyclic_subgroup]. *)
Global Instance Z1_commutative `{Funext} : Commutative (@group_sgop Z1)
  := commutative_iso_commutative iso_subgroup_incl_freegroupon.
(* [Funext] is used in [isfreegroupon_freegroup], but there is a comment there saying that it can be removed.  If that is done, don't need it here either. A different proof of this result, directly using the construction of the free group, could probably also avoid [Funext]. *)

Definition ab_Z1 `{Funext} : AbGroup
  := Build_AbGroup Z1 _.

(** The universal property of [ab_Z1]. *)
Lemma equiv_Z1_hom `{Funext} (A : AbGroup)
  : GroupIsomorphism (ab_hom ab_Z1 A) A.
Proof.
  snrapply Build_GroupIsomorphism'.
  - refine (_ oE (equiv_freegroup_rec A Unit)).
    symmetry. exact (Build_Equiv _ _ (Unit_rec A) _).
  - intros f g. cbn. reflexivity.
Defined.

(** Next we show that [equiv_Z1_hom] is natural. *)

Definition nat_to_Z1 : nat -> Z1 := fun n => grp_pow Z1_gen n.
Definition Z1_mul_nat (n : nat) : GroupHomomorphism Z1 Z1
  := Z1_rec (nat_to_Z1 n).

Lemma Z1_mul_nat_beta {A : AbGroup} (a : A) (n : nat)
  : FreeGroup_rec _ _  (fun _ => a) (nat_to_Z1 n) = ab_mul_nat n a.
Proof.
  induction n as [|n H].
  1: easy.
  refine (grp_pow_homo _ _ _ @ _); simpl.
  by rewrite grp_unit_r.
Defined.

(** Naturality of [equiv_Z1_hom]. *)
Lemma ab_mul_precomp `{Funext} (A : AbGroup) (n : Int)
  : equiv_Z1_hom A o (fun f => grp_homo_compose f (ab_mul n))
    == ab_mul n o equiv_Z1_hom A.
Proof.
  intro f; cbn.
  exact (ab_mul_homo n f _).
Defined.

(** [ab_Z1] is projective. *)
Lemma Z1_projective `{Funext} : IsAbProjective ab_Z1.
Proof.
  intros A B p f H1.
  pose proof (a := @center _ (H1 (f Z1_gen))).
  strip_truncations.
  snrefine (tr (Z1_rec a.1; _)).
  cbn beta. apply ap10.
  apply ap. (* of the coercion [grp_homo_map] *)
  apply path_homomorphism_from_free_group.
  simpl.
  intros [].
  refine (_ @ a.2).
  exact (ap p (grp_unit_r _)).
Defined.

(** * Finite cyclic groups *)

(** The [n]-th cyclic group is the cokernel of [Z1_mul_nat n]. *)
Definition cyclic `{Funext} (n : nat) : AbGroup
  := ab_cokernel (Z1_mul_nat n : ab_Z1 $-> ab_Z1).