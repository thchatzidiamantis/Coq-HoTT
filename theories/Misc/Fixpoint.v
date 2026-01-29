(** * Types for which self-maps have fixed points *)

From HoTT Require Import Basics Types.
Require Import Circle.
Require Import Suspension.
Require Import Truncations.Core Truncations.Connectedness Truncations.Constant.
(* Results from Truncations.Constant might be useful as this progresses. *)
Require Import HSpace.Core.
Require Import Homotopy.ClassifyingSpace.
Require Import Algebra.Groups.Group Subgroup Algebra.AbGroups.Centralizer.
Require Import Colimits.Quotient.
Require Import Pointed WildCat WildCat.Core Products WildCat.Adjoint.
Require Import Cubical.DPath PathSquare.
Require Export Classes.interfaces.canonical_names (SgOp, sg_op,
    MonUnit, mon_unit, LeftIdentity, left_identity, RightIdentity, right_identity,
    Negate, negate, Associative, simple_associativity, associativity,
    LeftInverse, left_inverse, RightInverse, right_inverse, Commutative, commutativity).
Export canonical_names.BinOpNotations.
Export Homotopy.ClassifyingSpace.ClassifyingSpaceNotation.

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

(** ** Consequences of the fixed point property *)

Definition helper_function {A : Type} (f : A -> Bool) (x y : A) : A -> A.
Proof.
  intro a.
    destruct (decidable_paths_bool (f a) (f y)) as [r | s].
    - exact x.
    - exact y.
Defined.

Definition constant_hasmerefixedpoints {A : Type}
  (fp_A : HasMereFixedPoints A) (f : A -> Bool)
  : forall x y, f x = f y.
Proof.
  intros x y.
  pose (g := helper_function f x y).
  specialize (fp_A g).
  strip_truncations.
  (* Since this term will come up later in the proof, we remember it. *)
  remember (decidable_paths_bool (f fp_A.1) (f y)) as d eqn:e.
  destruct d as [r | s].
  - refine (_ @ r).
    apply ap.
    rewrite fp_A.2^.
    unfold g, helper_function.
    rewrite e.
    reflexivity.
  - contradiction s.
    apply ap.
    rewrite fp_A.2^.
    unfold g, helper_function.
    rewrite e.
    reflexivity.
Admitted.

(** ** Unpointed functions between classifying spaces *)

Definition subtype_centralizer {G : Group} (H : G -> Type)
  : G -> Type
  (* Note the order of operations here, we do this to match the original proofs for the centraliser of an element. *)
  := fun g => (forall h : G, H h -> centralizer h g).

(* Need Funext to prove that this [subtype_centralizer] is [HProp]-valued. *)
Instance issubgroup_subtype_centralizer `{F : Funext}
  {G : Group} (H : G -> Type)
  : IsSubgroup (subtype_centralizer H).
Proof.
  srapply Build_IsSubgroup.
  - intros h Hh.
    exact (centralizer_unit h).
  - intros x y cx cy h Hh.
    exact (centralizer_sgop _ _ _ (cx h Hh) (cy h Hh)).
  - intros x Hx h Hh.
    exact (centralizer_inverse h x (Hx h Hh)).
Defined.

Definition subtype_centralizer_subgroup `{F : Funext}
  {G : Group} (H : G -> Type)
  := Build_Subgroup G (subtype_centralizer H) _.

(* remove this later *)
Definition b_subtype_centralizer `{F : Funext} {G : Group} (H : G -> Type)
  : Type.
Proof.
  apply ClassifyingSpace.
  apply (subgroup_group (G:=G)).
  exists (subtype_centralizer H); exact _.
Defined.

Definition grp_hom_centralizer_image_grp_hom `{F : Funext}
  {G H : Group} (f : G $-> H)
  : grp_prod (subtype_centralizer_subgroup (grp_image f)) G
    $-> H.
Proof.
  snapply Build_GroupHomomorphism.
  1,2: intros [[x Cx] y].
  - exact (x * f y).
  - intros [[z Cz] w]; cbn.
    refine (grp_assoc _ (f y) (f w) @ _ # ap _ (grp_homo_op _ _ _)).
    lhs_V exact (ap (.* f w) (grp_assoc x z (f y))).
    lhs_V exact (ap (fun r => x * r * (f w)) (Cz (f y) (tr (y; 1)))).
    lhs exact (ap (.* f w) (grp_assoc x (f y) z)).
    exact (grp_assoc (x * (f y)) z (f w))^.
Defined.

Definition grp_image_factorization {G H K : Group} (u : G $-> H) (v : H $-> K)
  : (v $o u) $== (grp_homo_restr v _) $o grp_homo_image_in u
  := fun x => idpath.

(* This is very slow. Is seems that it should also be simpler. *)
Definition eq_grp_image_homotopy {G H : Group} (u v : G $-> H) (p : u $== v)
  : subgroup_group (grp_image u) $<~> subgroup_group (grp_image v).
Proof.
  srapply Build_GroupIsomorphism.
  - unshelve snapply Build_GroupHomomorphism.
    { intros [h uh].
      exists h.
      strip_truncations; apply tr.
      exact (uh.1; (p _)^ @ uh.2). }
    { intros x y.
      snapply path_sigma_hprop.
      - exact _.
      - reflexivity. }
  - snapply isequiv_adjointify.
    { intros [h vh].
      exists h.
      strip_truncations; apply tr.
      exact (vh.1; (p _) @ vh.2). }
    { intro x.
      snapply path_sigma_hprop.
      - exact _.
      - reflexivity. }
    { intro x.
      snapply path_sigma_hprop.
      - exact _.
      - reflexivity. }
Defined.

(** u is v composed with an embedding (conjugation) so the images will be equivalent. *)
Definition equiv_image_grp_hom_conj `{F : Funext}
  {G H : Group} {u v : G $-> H}
  {c : H} (hc : forall g : G, u g = grp_conj c (v g))
  : subgroup_group (grp_image u) $<~> subgroup_group (grp_image v).
Proof.

Admitted.


Definition grp_hom_centralizer_image_grp_hom_conj `{F : Funext}
  {G H : Group} {u v : G $-> H}
  (conj : {h : H & forall g : G, u g = grp_conj h (v g)})
  : (subtype_centralizer_subgroup (fun h => {g : G & u g = h}))
    <~> (subtype_centralizer_subgroup (fun h => {g : G & v g = h})).
Proof.
(* I can probably be smarter about this and show that the subtypes formed by this are equivalent before applying subtype_centralizer_subgroup. See thing above. *)
  snapply Build_Equiv.
  - intros [x Cx].
    unfold subtype_centralizer_subgroup, subtype_centralizer, centralizer in *.
    cbn in *.
    exists x.
    intros h [k p].
Admitted.

Definition bg_grp_hom `{F : Funext} {G H : Group} (f : G $-> H)
  : b_subtype_centralizer (fun h => {g : G & f g = h}) -> (B G -> B H).
Proof.
  apply equiv_uncurry.
Admitted.

Definition groupreps `{U : Univalence} (G H : Group) : Type.
Proof.
  unshelve refine (@Quotient (G $-> H) _).
  intros a b.
  exact {h : H & forall g : G, a g = grp_conj h (b g)}.
Defined.

Definition idmap_fmap_grp_conj {G : Group} (g : G)
  : fmap B (grp_conj g) == idmap.
Proof.
  srapply ClassifyingSpace_ind_hset.
  - exact (bloop g).
  - intro x.
    rapply equiv_sq_dp^-1.
    cbn.
    apply (sq_ccGG (p0x:=bloop (grp_conj g x)) (p1x:=bloop x)).
    + by rewrite ClassifyingSpace_rec_beta_bloop.
    + exact (ap_idmap _)^.
    + apply equiv_sq_path; cbn.
      rhs_V rapply (bloop_pp _ _); lhs rapply (bloop_pp _ _)^.
      by rhs rapply (ap bloop (grp_inv_gV_g _ g)).
Defined.

(* This map should be an equivalence on [pi 0]. *)
Definition rep_bg_to_bh `{U : Univalence} (G H : Group)
  : groupreps G H -> Trunc 0 (B G -> B H).
Proof.
  unshelve refine (Quotient_rec _ _ _ _).
  - intro f.
    apply tr.
    exact (fmap B (a := G) (b := H) f).
  - intros a b [h r].
    apply ap.
    apply path_forall.
    lhs' exact (fmap2 (g:=grp_conj h $o b) B r).
    lhs' exact (fmap_comp B b (grp_conj h)).
    (* Define an unpointed B functor by composing with [pType -> Type]. *)
    intro x.
    exact (idmap_fmap_grp_conj h _).
Defined.

Definition isequiv_rep_bg_to_bh `{U : Univalence} (G H : Group)
  : IsEquiv (rep_bg_to_bh G H).
Proof.
  apply equiv_contr_map_isequiv.
  intro f.
  strip_truncations.
  generalize (merely_path_is0connected (B H) (f bbase) bbase).
  intro q.
  strip_truncations.
  srapply Build_Contr.
  - unshelve econstructor.
    { unfold groupreps.
      apply class_of.
      apply equiv_grp_homo_pmap_bg.
      srapply Build_pMap.
      1: exact f.
      exact q. }
    { unfold rep_bg_to_bh.
      admit. }
  - 
  (* Do this in a separate lemma, generalising the first map (any two maps that are sent to the same thing are conjugate). *)
    intros [u p].
    srapply path_sigma_hprop.
    unfold ".1".
    snapply (path_in_class_of _ _ _ _)^.
    1,2,3,4: admit.
Admitted.

(** * B preserves products *)

(** Right adjoints preserve products *)











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

