(** * Types for which self-maps have fixed points *)

From HoTT Require Import Basics Types.
Require Import Circle.
Require Import Suspension.
Require Import Truncations.Core Truncations.Connectedness Truncations.Constant.
(* Results from Truncations.Constant might be useful as this progresses. *)
Require Import HSpace.Core.
Require Export Classes.interfaces.canonical_names (SgOp, sg_op,
    MonUnit, mon_unit, LeftIdentity, left_identity, RightIdentity, right_identity,
    Negate, negate, Associative, simple_associativity, associativity,
    LeftInverse, left_inverse, RightInverse, right_inverse, Commutative, commutativity).
Export canonical_names.BinOpNotations.

Local Open Scope pointed_scope.
Local Open Scope trunc_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

(** ** Basic definitions *)

(* This is the strongest possible notion. *)
Definition HasFixedPoints (A : Type) := forall (f : A -> A), FixedBy f.

(* Should coincide with [HasMereIndexedFixedPoints] for idmap. *)
Definition HasMereFixedPoints (A : Type)
  := forall (f : A -> A), merely (FixedBy f).

Definition HasFamilyFixedPoints {X A : Type} (F : X -> A -> A)
  := forall x : X, FixedBy (F x).

Definition MerelyHasIndexedFixedPoints (X A : Type)
  := merely (forall (C : X -> A -> A), HasFamilyFixedPoints C).

(* Is this equivalent to also haveing a [merely] inside [HasFamilyFixedPoints]? *)
Definition HasMereIndexedFixedPoints (X A : Type)
  := forall C : X -> A -> A, merely (HasFamilyFixedPoints C).

Definition HasIndexedFixedPoints (X A : Type)
  := forall (C : X -> A -> A), HasFamilyFixedPoints C.

Definition hasfixedpoints_hasfullindexedfixedpoints_ptype {X : pType} {A : Type}
  (ifp : HasIndexedFixedPoints X A)
  : HasFixedPoints A
  := fun f => ifp (fun _ => f) (point X).

Definition test1 {X A : Type} (mX : merely X)
  (ifp : MerelyHasIndexedFixedPoints X A)
  : merely (HasFixedPoints A).
Proof.
  strip_truncations.
  apply tr.
  unshelve refine (hasfixedpoints_hasfullindexedfixedpoints_ptype _).
  - snapply Build_pType.
    + exact X.
    + exact mX.
  - exact ifp.
Defined.

Definition test2 {X A : Type} (mX : merely X)
  (mifp : HasMereIndexedFixedPoints X A)
  : HasMereFixedPoints A.
Proof.
  intro f.
  specialize (mifp (fun _ => f)).
  strip_truncations.
  apply tr.
  exact (mifp mX).
Defined.

Definition hasfixedpoints_hasfamilyfixedpoints_idmap {A : Type}
  (fp : HasFamilyFixedPoints (idmap : (A -> A) -> (A -> A)))
  : HasFixedPoints A
  := fun f => fp f.

(** ** Examples *)

Definition hasfixedpoints_contr {A : Type} (c : Contr A)
  : HasFixedPoints A
  := fun f => (center A; (contr (f (center A)))^).

Definition test {A : Type} (P : A -> Type) (s : {a : A & merely (P a)})
  : merely (sig P).
Proof.
  destruct s as [a p].
  strip_truncations.
  exact (tr (a; p)).
Defined.

Definition hasmerelyfixedpoints_connected `{Univalence} (A : pType)
  `{IsConnected 0 A}
  : forall f : A -> A, {a : A & merely (f a = a)}
  := fun f => (point A; merely_path_is0connected A (f (point A)) (point A)).

Definition hasmerelyfixedpoints_hasmerefixedpoints {A : Type}
  (fp : forall f : A -> A, {a : A & merely (f a = a)})
  : HasMereFixedPoints A
  := fun f => test _ (fp f).

Definition hasmerefixedpoints_connected `{Univalence} {A : Type}
  `{mA : merely A} `{IsConnected 0 A}
  : HasMereFixedPoints A.
Proof.
  intro f.
  strip_truncations.
  pose (r := merely_path_is0connected A (f mA) mA).
  (* There has got to be a simpler way to do this. *)
  exact (test _ (mA; r)).
Defined.

Definition pointed_hasfixedpoints {A : Type} (F : HasFixedPoints A) : A
  := (F idmap).1.

Definition nofixedpoints_bool : ~ (HasFixedPoints Bool).
Proof.
  intro F.
  destruct (F negb) as [a pa]; induction a.
  1,2: by apply false_ne_true.
Defined.

(** ** Retracts *)

(** This maybe has a converse based on surjections? *)
Definition hasfamilyfixedpoints_comp {X A Y : Type} {C : X -> A -> A}
(* Order of assumptions here might not be optimal. *)
  (fp_C : HasFamilyFixedPoints C) (g : Y -> X)
  : HasFamilyFixedPoints (C o g)
  := fun x => (fp_C (g x)).

Definition hasfixedpoints_retract {A R : Type} {f : A -> R} {g : R -> A}
  (s : f o g == idmap) (fp_A : HasFixedPoints A)
  : HasFixedPoints R.
Proof.
  intro h.
  destruct (fp_A (g o h o f)) as [a p].
  exists (f a).
  exact ((s _)^ @ ap f p).
Defined.

Definition hasmereindexedfixedpoints_retract_1 {X A R : Type}
  {f : A -> R} {g : R -> A} (s : f o g == idmap)
  (fp_XA : HasMereIndexedFixedPoints X A)
  : HasMereIndexedFixedPoints X R.
Proof.
  intro C.
  specialize (fp_XA (fun x => g o (C x) o f)); strip_truncations.
  apply tr.
  intro x.
  exists (f (fp_XA x).1).
  exact ((s _)^ @ ap f (fp_XA x).2).
Defined.

Definition hasmereindexedfixedpoints_retract_2 {X Y A : Type}
  {f : X -> Y} {g : Y -> X} (s : f o g == idmap)
  (fp_XA : HasMereIndexedFixedPoints X A)
  : HasMereIndexedFixedPoints Y A.
Proof.
  intro C.
  specialize (fp_XA (fun x => C (f x))); strip_truncations.
  apply tr.
  intro y.
  exists  (fp_XA (g y)).1.
  refine ((apD10 (ap C (s _)) _)^ @ (fp_XA (g y)).2).
Defined.

Definition hasindexedmerefixedpoints_surjection {X Y A : Type}
  {f : X -> Y} (s : IsSurjection f)
  (fp_XA : HasMereIndexedFixedPoints X A)
  : forall C : Y -> A -> A, forall y : Y, merely (FixedBy (C y)).
Proof.
  intros C.
  apply (conn_map_elim (-1) f _).
  intro x.
  specialize (fp_XA (fun x => C (f x))); strip_truncations.
  exact (tr (fp_XA x)).
Defined.

(* Maybe use the thing above to prove this. *)
Definition hasmerefixedpoints_retract {A R : Type} {f : A -> R} {g : R -> A}
  (s : f o g == idmap) (fp_A : HasMereFixedPoints A)
  : HasMereFixedPoints R.
Proof.
  intro h.
  pose (fp := fp_A (g o h o f)); generalize fp.
  intro fp'; strip_truncations.
  apply test.
  exists (f fp'.1).
  exact (tr ((s _)^ @ ap f fp'.2)).
Defined.

(* Actually a logical equivalence by the work above. *)
Definition hasfamilyfixedpoints_section {X A R : Type}
(* Order of assumptions and naming here not optimal. *)
  {f : A -> R} {g : R -> A} {C : X -> R -> R}
  (s : f o g == idmap) (fp_C : HasFamilyFixedPoints C)
  : HasFamilyFixedPoints (fun x => g o (C x) o f).
Proof.
  intro x.
  destruct (fp_C x) as [a p].
  exists (g a).
  exact (ap g (ap (C x) (s a) @ p)).
Defined.

(** ** Products *)

Definition hasfixedpoints_hasfixedpoints_prod {A B : Type}
  (fp_AB : HasFixedPoints (A * B))
  : HasFixedPoints A.
Proof.
  refine (hasfixedpoints_retract (f:=fst) (g:=fun x => (x, snd (fp_AB idmap).1)) _ fp_AB).
  by cbn.
Defined.

(* Can I also reproduce this as an instance of retracts? *)
Definition hasmerefixedpoints_hasmerefixedpoints_prod {A B : Type}
  (fp_AB : HasMereFixedPoints (A * B))
  : HasMereFixedPoints A.
Proof.
  intro f.
  specialize (fp_AB (fun ab => (f (fst ab), snd ab))).
  strip_truncations; apply tr.
  exists (fst (fp_AB).1).
  exact (ap fst (fp_AB.2)).
Defined.

Definition hasmereindexedfixedpoints_hasmereindexedfixedpoints_prod_1
  {X A B : Type} (fp_AB : HasMereIndexedFixedPoints X (A * B))
  : HasMereIndexedFixedPoints X A.
Proof.
  intro C.
  (* Is it worth recording this for a single family? *)
  specialize (fp_AB (fun x => fun ab => (C x (fst ab), snd ab))).
  strip_truncations; apply tr.
  intro x.
  exists (fst (fp_AB x).1).
  exact (ap fst (fp_AB x).2).
Defined.

Definition hasmereindexedfixedpoints_hasmereindexedfixedpoints_prod_2
  {X A Y : Type} {mY : merely Y} (fp_AB : HasMereIndexedFixedPoints (X * Y) A)
  : HasMereIndexedFixedPoints X A.
Proof.
  intro C.
  (* Is it worth recording this for a single family? *)
  specialize (fp_AB (fun xy => fun a => C (fst xy) a)).
  strip_truncations; apply tr.
  intro x.
  exact (fp_AB (x, mY)).
Defined.

Definition prod_help1 {A B : Type} (f : A * B -> A * B) (b : B)
  : A -> A
  := fun x => fst (f (x, b)).

Definition prod_help2 {A B : Type} (f : A * B -> A * B) (a : A)
  : B -> B
  := fun y => snd (f (a, y)).

Definition hasfixedpoints_prod_hasfixedpoints {A B : Type}
  (fp_A : HasFixedPoints A) (fp_B : HasFixedPoints B)
  : HasFixedPoints (A * B).
Proof.
  intro f.
  destruct (fp_A (fun x => prod_help1 f (fp_B (prod_help2 f x)).1 x)) as [a p].
  destruct (fp_B (prod_help2 f a)) as [b q]; cbn in p.
  exists (a, b).
  exact (path_prod (f (a, b)) (a, b) p q).
Defined.

(* I wonder if I could recreate a counterexample to this. Again, would be true with the [merely] inside the FixedBy (see below). Is that a sensible definition? *)
Definition prod_test_converse'2 {A B : Type}
  (fp_A : HasMereFixedPoints A) (fp_B : HasMereFixedPoints B)
  : HasMereFixedPoints (A * B).
Admitted.

Definition prod_test_converse' {A B : Type}
  (fp_A : forall f : A -> A, {a : A & merely (f a = a)})
  (fp_B : forall g : B -> B, {b : B & merely (g b = b)})
  : forall h : A * B -> A * B, {ab : A * B & merely (h ab = ab)}.
Proof.
  intro h.
  destruct (fp_A (fun x => prod_help1 h (fp_B (prod_help2 h x)).1 x)) as [a p].
  destruct (fp_B (prod_help2 h a)) as [b q]; cbn in p.
  exists (a, b).
  strip_truncations; apply tr.
  exact (path_prod (h (a, b)) (a, b) p q).
Defined.

(** ** The total space of all fixed points *)

Definition Fixpoints (A : Type) := {f : A -> A & FixedBy f}.

Definition fixpoints_base (A : Type) : A -> Fixpoints A
  := fun a => (idmap; (a; idpath)).

Definition isretr_base_fixpoints (A : Type)
  : (fun fp => fp.2.1) o fixpoints_base A == idmap
  := fun _ => idpath.

Definition what {A : Type} (fp_A : HasFixedPoints A)
  : (A -> A) -> Fixpoints A
  := fun f => (f; (fp_A f)).

Definition issect_what {A : Type} (fp_A : HasFixedPoints A)
  : pr1 o what fp_A == idmap
  := fun _ => idpath.

(** ** Lawvere's fixed point theorem *)

Definition lawvere_fp {A B : Type} (F : A -> (A -> B))
  (s : forall h : A -> B, {a : A & F a = h})
  : HasFixedPoints B.
Proof.
  intro g.
  pose (k := fun (x : A) => g (F x x)).
  exists (F (s k).1 (s k).1).
  exact (ap10 (s k).2 (s k).1)^.
Defined.




















(* Theorem 8.3 from Szymik could correspond to a modality-based result? *)

(* What about Σ-types? *)

(* Is every such type connected? Is every such type not disconnected? Probably, following the [Bool] example. Is every connected type with fixed points contractible? *)

(* Definition circle_family : Circle -> Circle -> Circle.
Proof.
  intros x y; revert x. (* Could instead just do intro x. *)
  srapply Circle_rec.
  - exact y.
  - revert y; srapply Circle_ind; cbn beta.
    + exact loop.
    + transport_paths lr.
      reflexivity.
Defined.

Definition circle_family_V : Circle -> Circle -> Circle.
Proof.
  intros x y; revert x. (* Could instead just do intro x. *)
  srapply Circle_rec.
  - exact y.
  - revert y; srapply Circle_ind; cbn beta.
    + exact loop^.
    + transport_paths lr.
      exact (concat_pV _ @ (concat_Vp _)^).
Defined.

Definition concat_Vp_inv {A : Type} {a : A} {p q : a = a} (h : p = q)
  : p^ @ q = idpath.
Proof.
  destruct h; destruct p.
  reflexivity.
Defined.

Definition circle_family_pt_l (c : Circle) : circle_family base c = c := idpath.

Definition circle_family_pt_r (c : Circle)
  : circle_family c base = c.
(* I'd probably rather have that one compute definitionally. *)
Proof.
  revert c; srapply Circle_ind; cbn beta.
  - reflexivity.
  - lhs napply (transport_paths_Flr (f:=fun x => circle_family x base)).
    rewrite ap_apply_Fl. (* Key step to allow the next line to work. *)
    rewrite concat_p1.
    apply concat_Vp_inv.
    unfold ap10.
    Check (ap circle_family loop).
    admit.
Admitted.

(* This could be immediate using isequiv_hspace_left_op or something *)
Definition isequiv_circle_family `{Funext} (c : Circle) : IsEquiv (circle_family c).
Proof.
  apply (isequiv_adjointify _ (circle_family_V c)).
  - revert c.
    snapply Circle_ind.
    + exact (fun _ => idpath).
    + admit.
  - revert c.
    snapply Circle_ind.
    + exact (fun _ => idpath).
    + admit.
Admitted.

Definition iscontr_hasfixedpoints_invertible_hspace `{Univalence} {A : pType}
  `{IsHSpace A} (e : forall a : A, IsEquiv (.* a)) (fp_A : HasFixedPoints A)
  : Contr A.
Proof.
  snapply Build_Contr.
  - exact (point A).
  - intro a.
    pose (f := fun x => (fp_A (x *.)).1).
    assert (pf : forall x : A, x * (f x) = f x).
    { exact (fun x => (fp_A (x *.)).2). }
    specialize (pf a).
admit.
 *)

