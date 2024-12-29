Require Import Basics.Overture Basics.Tactics.
Require Import Types.Forall Types.Sigma Types.Prod.
Require Import WildCat.Core WildCat.Equiv WildCat.Monoidal WildCat.Bifunctor.
Require Import WildCat.NatTrans WildCat.MonoidalTwistConstruction.
Require Import Algebra.Groups.Group Algebra.Groups.QuotientGroup.
Require Import Algebra.AbGroups.AbelianGroup Algebra.AbGroups.Biproduct.
Require Import Algebra.AbGroups.AbHom Algebra.AbGroups.FreeAbelianGroup.
Require Import Algebra.AbGroups.Abelianization Algebra Algebra.Groups.FreeGroup.
Require Import Colimits.Quotient.
Require Import Spaces.List.Core Spaces.Int.
Require Import AbGroups.Z.
Require Import Truncations.

Local Open Scope mc_add_scope.

(** * The Tensor Product of Abelian Groups *)

(** Various maps [A * B → C] from the cartesian product of two abelian groups to another abelian group are "biadditive" (also called "bilinear"), meaning that they are group homomorphisms when we fix the left or right argument.

The tensor product of abelian groups is a construction that produces an abelian group [A ⊗ B] along with a biadditive map [A * B -> A ⊗ B] which is initial among biadditive maps from [A * B].  This means that any biadditive map [A * B → C] factors uniquely through the tensor product via a group homomorphism [A ⊗ B -> C].

Biadditive functions appear in all sorts of contexts ranging from linear algebra to analysis. Therefore having a way to systematically study them is very useful. *)

(** ** Construction *)

(** We define the tensor product of abelian groups as a quotient of the free abelian group on pairs of elements of the two groups by the subgroup generated by the biadditive pairs. *)

(** Here we define the subgroup of biadditive pairs in two steps. *)
Definition family_biadditive_pairs {A B : AbGroup}
  : FreeAbGroup (A * B) -> Type.
Proof.
  intros x.
  refine ((exists (a1 a2 : A) (b : B), _) + exists (a : A) (b1 b2 : B), _)%type. 
  - refine (- _ + (_ + _) = x).
    1-3: apply freeabgroup_in.
    + exact (a1 + a2, b).
    + exact (a1, b).
    + exact (a2, b).
  - refine (- _ + (_ + _) = x).
    1-3: apply freeabgroup_in.
    + exact (a, b1 + b2).
    + exact (a, b1).
    + exact (a, b2).
Defined.

Definition subgroup_biadditive_pairs {A B : AbGroup}
  : Subgroup (FreeAbGroup (A * B))
  := subgroup_generated family_biadditive_pairs.

(** The tensor product [ab_tensor_prod A B] of two abelian groups [A] and [B] is defined to be a quotient of the free abelian group on pairs of elements [A * B] by the subgroup of biadditive pairs. *)
Definition ab_tensor_prod (A B : AbGroup) : AbGroup
  := QuotientAbGroup (FreeAbGroup (A * B)) subgroup_biadditive_pairs.

Arguments ab_tensor_prod A B : simpl never.

(** The tensor product of [A] and [B] contains formal sums and differences of pairs of elements from [A] and [B]. We denote these pairs as "simple tensors" and name them [tensor]. *)
Definition tensor {A B : AbGroup} : A -> B -> ab_tensor_prod A B
  := fun a b => grp_quotient_map (freeabgroup_in (a, b)).

(** ** Properties of tensors *)

(** The characterizing property of simple tensors are that they are biadditive in their arguments. *)

(** A [tensor] of a sum distributes over the sum on the left. *) 
Definition tensor_dist_l {A B : AbGroup} (a : A) (b b' : B)
  : tensor a (b + b') = tensor a b + tensor a b'.
Proof.
  apply qglue, tr.
  apply sgt_in.
  right.
  by exists a, b, b'.
Defined.

(** A [tensor] of a sum distributes over the sum on the right. *)
Definition tensor_dist_r {A B : AbGroup} (a a' : A) (b : B)
  : tensor (a + a') b = tensor a b + tensor a' b.
Proof.
  apply qglue, tr.
  apply sgt_in.
  left.
  by exists a, a', b.
Defined.

(** Tensoring on the left is a group homomorphism. *)
Definition grp_homo_tensor_l {A B : AbGroup} (a : A)
  : B $-> ab_tensor_prod A B.
Proof.
  snrapply Build_GroupHomomorphism.
  - exact (fun b => tensor a b).
  - intros b b'.
    nrapply tensor_dist_l.
Defined. 

(** Tensoring on the right is a group homomorphism. *)
Definition grp_homo_tensor_r {A B : AbGroup} (b : B)
  : A $-> ab_tensor_prod A B.
Proof.
  snrapply Build_GroupHomomorphism.
  - exact (fun a => tensor a b).
  - intros a a'.
    nrapply tensor_dist_r.
Defined.

(** Tensors preserve negation in the left argument. *)
Definition tensor_neg_l {A B : AbGroup} (a : A) (b : B)
  : tensor (-a) b = - tensor a b
  := grp_homo_inv (grp_homo_tensor_r b) a.

(** Tensors preserve negation in the right argument. *)
Definition tensor_neg_r {A B : AbGroup} (a : A) (b : B)
  : tensor a (-b) = - tensor a b
  := grp_homo_inv (grp_homo_tensor_l a) b.

(** Tensoring by zero on the left is zero. *)
Definition tensor_zero_l {A B : AbGroup} (b : B)
  : tensor (A:=A) 0 b = 0
  := grp_homo_unit (grp_homo_tensor_r b).

(** Tensoring by zero on the right is zero. *)
Definition tensor_zero_r {A B : AbGroup} (a : A)
  : tensor (B:=B) a 0 = 0
  := grp_homo_unit (grp_homo_tensor_l a).

(** The [tensor] map is biadditive and therefore can be written in a curried form using the internal abelian group hom. *)
Definition grp_homo_tensor `{Funext} {A B : AbGroup}
  : A $-> ab_hom B (ab_tensor_prod A B). 
Proof.
  snrapply Build_GroupHomomorphism.
  - intros a.
    snrapply Build_GroupHomomorphism.
    + exact (tensor a).
    + nrapply tensor_dist_l.
  - intros a a'.
    apply equiv_path_grouphomomorphism.
    intros b.
    nrapply tensor_dist_r.
Defined.

(** ** Induction principles *)

(** Here we write down some induction principles to help us prove lemmas about the tensor product. Some of these are quite specialised but are patterns that appear often in practice. *) 

(** Our main recursion principle states that in order to build a homomorphism out of the tensor product, it is sufficient to provide a map out of the direct product which is biadditive, that is, a map that preserves addition in each argument of the product. *)

(** We separate out the proof of this part, so we can make it opaque. *)
Definition ab_tensor_prod_rec_helper {A B C : AbGroup}
  (f : A -> B -> C)
  (l : forall a b b', f a (b + b') = f a b + f a b')
  (r : forall a a' b, f (a + a') b = f a b + f a' b)
  (x : FreeAbGroup (A * B)) (insg : subgroup_biadditive_pairs x)
  : grp_homo_abel_rec (FreeGroup_rec (uncurry f)) x = mon_unit.
Proof.
  set (abel_rec := grp_homo_abel_rec (FreeGroup_rec (uncurry f))).
  strip_truncations.
  induction insg as [ x biad | | g h insg_g IHg insg_h IHh ].
  - destruct biad as [ [ a [ a' [ b p ] ] ] | [ a [ b [ b' p ] ] ] ].
    all: destruct p; simpl.
    all: apply grp_moveL_M1^-1%equiv; symmetry.
    1: apply r.
    apply l.
  - nrapply grp_homo_unit.
  - rewrite grp_homo_op, grp_homo_inv.
    apply grp_moveL_1M^-1.
    exact (IHg @ IHh^).
Defined.

Opaque ab_tensor_prod_rec_helper.

Definition ab_tensor_prod_rec {A B C : AbGroup}
  (f : A -> B -> C)
  (l : forall a b b', f a (b + b') = f a b + f a b')
  (r : forall a a' b, f (a + a') b = f a b + f a' b) 
  : ab_tensor_prod A B $-> C.
Proof.
  unfold ab_tensor_prod.
  snrapply grp_quotient_rec.
  - snrapply FreeAbGroup_rec.
    exact (uncurry f).
  - unfold normalsubgroup_subgroup.
    apply ab_tensor_prod_rec_helper; assumption.
Defined.

(** A special case that arises. *)
Definition ab_tensor_prod_rec' {A B C : AbGroup}
  (f : A -> (B $-> C))
  (l : forall a a' b, f (a + a') b = f a b + f a' b)
  : ab_tensor_prod A B $-> C.
Proof.
  refine (ab_tensor_prod_rec f _ l).
  intro a; apply grp_homo_op.
Defined.

(** We give an induction principle for an hprop-valued type family [P].  It may be surprising at first that we only require [P] to hold for the simple tensors [tensor a b] and be closed under addition.  It automatically follows that [P 0] holds (since [tensor 0 0 = 0]) and that [P] is closed under negation (since [tensor -a b = - tensor a b]). This induction principle says that the simple tensors generate the tensor product as a semigroup. *)
Definition ab_tensor_prod_ind_hprop {A B : AbGroup}
  (P : ab_tensor_prod A B -> Type)
  {H : forall x, IsHProp (P x)}
  (Hin : forall a b, P (tensor a b))
  (Hop : forall x y, P x -> P y -> P (x + y))
  : forall x, P x.
Proof.
  unfold ab_tensor_prod.
  srapply grp_quotient_ind_hprop.
  srapply Abel_ind_hprop; cbn beta.
  set (tensor_in := grp_quotient_map $o abel_unit : FreeGroup (A * B) $-> ab_tensor_prod A B).
  change (forall x, P (tensor_in x)).
  srapply FreeGroup_ind_hprop'; intros w; cbn beta.
  induction w.
  - (* The goal here is [P 0], so we use [Hin 0 0 : P (tensor 0 0)]. *)
    exact (transport P (tensor_zero_l 0) (Hin 0 0)).
  - change (P (tensor_in (freegroup_eta [a]%list + freegroup_eta w))).
    (* This [rewrite] is [reflexivity], but the [Defined] is slow if [change] is used instead. *)
    rewrite grp_homo_op.
    destruct a as [[a b]|[a b]].
    + change (P (tensor_in (freegroup_in (a, b)) + tensor_in (freegroup_eta w))).
      apply Hop; trivial.
      apply Hin.
    + change (P (tensor_in (- freegroup_in (a, b)) + tensor_in (freegroup_eta w))).
      (* This [rewrite] is reflexivity, but using [change] to achieve this is slow and slows down the Defined line. *)
      rewrite grp_homo_inv.
      apply Hop; trivial.
      rewrite <- tensor_neg_l.
      apply Hin.
Defined.

(** As a commonly occuring special case of the above induction principle, we have the case when the predicate in question is showing that two group homomorphisms out of the tensor product are homotopic. In order to do this, it suffices to show it only for simple tensors. The homotopy is closed under addition, so we don't need to hypothesise anything else. *)
Definition ab_tensor_prod_ind_homotopy {A B G : AbGroup}
  {f f' : ab_tensor_prod A B $-> G}
  (H : forall a b, f (tensor a b) = f' (tensor a b))
  : f $== f'.
Proof.
  nrapply ab_tensor_prod_ind_hprop.
  - exact _.
  - exact H.
  - intros x y; apply grp_homo_op_agree.
Defined.

(** As an even more specialised case, we occasionally have the second homomorphism being a sum of abelian group homomorphisms. In those cases, it is easier to use this specialised lemma. *)
Definition ab_tensor_prod_ind_homotopy_plus {A B G : AbGroup}
  {f f' f'' : ab_tensor_prod A B $-> G}
  (H : forall a b, f (tensor a b) = f' (tensor a b) + f'' (tensor a b))
  : forall x, f x = f' x + f'' x
  := ab_tensor_prod_ind_homotopy (f':=f' + f'') H.

(** Here we give an induction principle for a triple tensor, a.k.a a dependent trilinear function. *)
Definition ab_tensor_prod_ind_hprop_triple {A B C : AbGroup}
  (P : ab_tensor_prod A (ab_tensor_prod B C) -> Type)
  (H : forall x, IsHProp (P x))
  (Hin : forall a b c, P (tensor a (tensor b c)))
  (Hop : forall x y, P x -> P y -> P (x + y))
  : forall x, P x.
Proof.
  rapply (ab_tensor_prod_ind_hprop P).
  - intros a.
    rapply (ab_tensor_prod_ind_hprop (fun x => P (tensor _ x))).
    + nrapply Hin.
    + intros x y Hx Hy.
      rewrite tensor_dist_l.
      by apply Hop.
  - exact Hop.
Defined.

(** Similar to before, we specialise the triple tensor induction principle for proving homotopies of trilinear/triadditive functions. *)
Definition ab_tensor_prod_ind_homotopy_triple {A B C G : AbGroup}
  {f f' : ab_tensor_prod A (ab_tensor_prod B C) $-> G}
  (H : forall a b c, f (tensor a (tensor b c)) = f' (tensor a (tensor b c)))
  : f $== f'.
Proof.
  nrapply ab_tensor_prod_ind_hprop_triple.
  - exact _.
  - exact H.
  - intros x y; apply grp_homo_op_agree.
Defined.

(** As explained for the biadditive and triadditive cases, we also derive an induction principle for quadruple tensors giving us dependent quadrilinear maps. *)
Definition ab_tensor_prod_ind_hprop_quad {A B C D : AbGroup}
  (P : ab_tensor_prod A (ab_tensor_prod B (ab_tensor_prod C D)) -> Type)
  (H : forall x, IsHProp (P x))
  (Hin : forall a b c d, P (tensor a (tensor b (tensor c d))))
  (Hop : forall x y, P x -> P y -> P (x + y))
  : forall x, P x.
Proof.
  rapply (ab_tensor_prod_ind_hprop P).
  - intros a.
    nrapply (ab_tensor_prod_ind_hprop_triple (fun x => P (tensor _ x))).
    + intro x; apply H.
    + nrapply Hin.
    + intros x y Hx Hy.
      rewrite tensor_dist_l.
      by apply Hop.
  - exact Hop.
Defined.

(** To construct a homotopy between quadrilinear maps we need only check equality for the quadruple simple tensors. *)
Definition ab_tensor_prod_ind_homotopy_quad {A B C D G : AbGroup}
  {f f' : ab_tensor_prod A (ab_tensor_prod B (ab_tensor_prod C D)) $-> G}
  (H : forall a b c d, f (tensor a (tensor b (tensor c d)))
    = f' (tensor a (tensor b (tensor c d))))
  : f $== f'.
Proof.
  nrapply (ab_tensor_prod_ind_hprop_quad (fun _ => _)).
  - exact _.
  - exact H.
  - intros x y; apply grp_homo_op_agree.
Defined.

(** ** Universal Property of the Tensor Product *)

(** A function of two variables is biadditive if it preserves the operation in each variable. *)
Class IsBiadditive {A B C : Type} `{SgOp A, SgOp B, SgOp C} (f : A -> B -> C) := {
  isbiadditive_l :: forall b, IsSemiGroupPreserving (flip f b);
  isbiadditive_r :: forall a, IsSemiGroupPreserving (f a);  
}.

Definition issig_IsBiadditive {A B C : Type} `{SgOp A, SgOp B, SgOp C}
  (f : A -> B -> C)
  : _ <~> IsBiadditive f
  := ltac:(issig).

(** The truncation level of the [IsBiadditive f] predicate is determined by the truncation level of the codomain. This will almost always be a hset. *)
Global Instance istrunc_isbiadditive `{Funext}
  {A B C : Type} `{SgOp A, SgOp B, SgOp C}
  (f : A -> B -> C) n `{IsTrunc n.+1 C}
  : IsTrunc n (IsBiadditive f).
Proof.
  nrapply istrunc_equiv_istrunc.
  1: rapply issig_IsBiadditive.
  unfold IsSemiGroupPreserving.
  exact _.
Defined.

(** The simple tensor map is biadditive. *)
Global Instance isbiadditive_tensor (A B : AbGroup)
  : IsBiadditive (@tensor A B) := {|
  isbiadditive_l := fun b a a' => tensor_dist_r a a' b;
  isbiadditive_r := tensor_dist_l;
|}.

(** The type of biadditive maps. *)
Record Biadditive (A B C : Type) `{SgOp A, SgOp B, SgOp C} := {
  biadditive_fun :> A -> B -> C;
  biadditive_isbiadditive :: IsBiadditive biadditive_fun;
}.

Definition issig_Biadditive {A B C : Type} `{SgOp A, SgOp B, SgOp C}
  : _ <~> Biadditive A B C
  := ltac:(issig).

Definition biadditive_ab_tensor_prod {A B C : AbGroup}
  : (ab_tensor_prod A B $-> C) -> Biadditive A B C.
Proof.
  intros f.
  exists (fun x y => f (tensor x y)).
  snrapply Build_IsBiadditive.
  - intros b a a'; simpl.
    lhs nrapply (ap f).
    1: nrapply tensor_dist_r.
    nrapply grp_homo_op.
  - intros a a' b; simpl.
    lhs nrapply (ap f).
    1: nrapply tensor_dist_l.
    nrapply grp_homo_op.
Defined.

(** The universal property of the tensor product is that biadditive maps between abelian groups are in one-to-one corresondance with maps out of the tensor product. In this sense, the tensor product is the most perfect object describing biadditive maps between two abelian groups. *)
Definition equiv_ab_tensor_prod_rec `{Funext} (A B C : AbGroup)
  : Biadditive A B C <~> (ab_tensor_prod A B $-> C).
Proof.
  snrapply equiv_adjointify.
  - intros [f [l r]].
    exact (ab_tensor_prod_rec f r (fun a a' b => l b a a')).
  - snrapply biadditive_ab_tensor_prod.
  - intros f.
    snrapply equiv_path_grouphomomorphism.
    snrapply ab_tensor_prod_ind_homotopy.
    intros a b; simpl.
    reflexivity.
  - intros [f [l r]].
    snrapply (equiv_ap_inv' issig_Biadditive).
    rapply path_sigma_hprop; simpl.
    reflexivity.
Defined.

(** ** Functoriality of the Tensor Product *)

(** The tensor product produces a bifunctor and we will later show that it gives a symmetric monoidal structure on the category of abelian groups. *)

(** Given a pair of maps, we can produce a homomorphism between the pairwise tensor products of the domains and codomains. *) 
Definition functor_ab_tensor_prod {A B A' B' : AbGroup}
  (f : A $-> A') (g : B $-> B')
  : ab_tensor_prod A B $-> ab_tensor_prod A' B'.
Proof.
  snrapply ab_tensor_prod_rec'.
  - intro a.
    exact (grp_homo_tensor_l (f a) $o g).
  - intros a a' b; hnf.
    rewrite grp_homo_op.
    nrapply tensor_dist_r.
Defined.

(** 2-functoriality of the tensor product. *)
Definition functor2_ab_tensor_prod {A B A' B' : AbGroup}
  {f f' : A $-> A'} (p : f $== f') {g g' : B $-> B'} (q : g $== g')
  : functor_ab_tensor_prod f g $== functor_ab_tensor_prod f' g'.
Proof.
  snrapply ab_tensor_prod_ind_homotopy.
  intros a b; simpl.
  exact (ap011 tensor (p _) (q _)).
Defined.

(** The tensor product functor preserves identity morphisms. *)
Definition functor_ab_tensor_prod_id (A B : AbGroup)
  : functor_ab_tensor_prod (Id A) (Id B) $== Id (ab_tensor_prod A B).
Proof.
  snrapply ab_tensor_prod_ind_homotopy.
  intros a b; simpl.
  reflexivity.
Defined.

(** The tensor product functor preserves composition. *)
Definition functor_ab_tensor_prod_compose {A B C A' B' C' : AbGroup}
  (f : A $-> B) (g : B $-> C) (f' : A' $-> B') (g' : B' $-> C')
  : functor_ab_tensor_prod (g $o f) (g' $o f')
    $== functor_ab_tensor_prod g g' $o functor_ab_tensor_prod f f'.
Proof.
  snrapply ab_tensor_prod_ind_homotopy.
  intros a b; simpl.
  reflexivity.
Defined.

(** The tensor product functor is a 0-bifunctor. *)
Global Instance is0bifunctor_ab_tensor_prod : Is0Bifunctor ab_tensor_prod.
Proof.
  rapply Build_Is0Bifunctor'.
  snrapply Build_Is0Functor.
  intros [A B] [A' B'] [f g].
  exact (functor_ab_tensor_prod f g).
Defined.

(** The tensor product functor is a bifunctor. *)
Global Instance is1bifunctor_ab_tensor_prod : Is1Bifunctor ab_tensor_prod.
Proof.
  rapply Build_Is1Bifunctor'.
  snrapply Build_Is1Functor.
  - intros AB A'B' fg f'g' [p q].
    exact (functor2_ab_tensor_prod p q).
  - intros [A B].
    exact (functor_ab_tensor_prod_id A B).
  - intros AA' BB' CC' [f g] [f' g'].
    exact (functor_ab_tensor_prod_compose f f' g g').
Defined.

(** ** Symmetry of the Tensor Product *)

(** The tensor product is symmetric in that the order in which we take the tensor shouldn't matter upto isomorphism. *)

(** We can define a swap map which swaps the order of simple tensors. *)
Definition ab_tensor_swap {A B} : ab_tensor_prod A B $-> ab_tensor_prod B A.
Proof.
  snrapply ab_tensor_prod_rec. 
  - exact (flip tensor).
  - intros a b b'.
    apply tensor_dist_r.
  - intros a a' b.
    apply tensor_dist_l.
Defined.

(** [ab_tensor_swap] is involutive. *)
Definition ab_tensor_swap_swap {A B}
  : ab_tensor_swap $o @ab_tensor_swap A B $== Id _. 
Proof.
  snrapply ab_tensor_prod_ind_homotopy.
  reflexivity.
Defined. 

(** [ab_tensor_swap] is natural in both arguments. This means that it also acts on tensor functors. *)
Definition ab_tensor_swap_natural {A B A' B'} (f : A $-> A') (g : B $-> B')
  : ab_tensor_swap $o functor_ab_tensor_prod f g
    $== functor_ab_tensor_prod g f $o ab_tensor_swap.
Proof.
  snrapply ab_tensor_prod_ind_homotopy.
  simpl. (* This speeds up the [reflexivity] and the [Defined]. *)
  reflexivity.
Defined.

(** The swap map gives us a symmetric braiding on the category of abelian groups. We will later show it is a full symmetric monoidal category. *)
Global Instance symmetricbraiding_ab_tensor_prod : SymmetricBraiding ab_tensor_prod.
Proof.
  snrapply Build_SymmetricBraiding.
  - snrapply Build_NatTrans.
    + intro; exact ab_tensor_swap.
    + snrapply Build_Is1Natural.
      intros; nrapply ab_tensor_swap_natural.
  - intros; nrapply ab_tensor_swap_swap.
Defined. 

(** ** Twisting Triple Tensors *)

(** In order to construct the symmetric monoidal category, we will use what is termed the "Twist construction" in Monoidal.v. This simplifies the data of a symmetric monoidal category by constructing it from simpler parts. For instance, instead of having to prove full associativity [(A ⊗ B) ⊗ C $-> A ⊗ (B ⊗ C)], we can provide a twist map [A ⊗ (B ⊗ C) $-> B ⊗ (A ⊗ C)] and use the symmetric braiding we have so far to prove associativity. *)

(** In order to be more efficient whilst unfolding definitions, we break up the definition of a twist map into its components. *)

Local Definition ab_tensor_prod_twist_map {A B C : AbGroup}
  : A -> (ab_tensor_prod B C $-> ab_tensor_prod B (ab_tensor_prod A C)).
Proof.
  intros a.
  snrapply ab_tensor_prod_rec'.
  - intros b.
    exact (grp_homo_tensor_l b $o grp_homo_tensor_l a).
  - intros b b' c; hnf.
    nrapply tensor_dist_r.
Defined.

Local Definition ab_tensor_prod_twist_map_additive_l {A B C : AbGroup}
  (a a' : A) (b : ab_tensor_prod B C)
  : ab_tensor_prod_twist_map (a + a') b
    = ab_tensor_prod_twist_map a b + ab_tensor_prod_twist_map a' b.
Proof.  
  revert b.
  nrapply ab_tensor_prod_ind_homotopy_plus.
  intros b c.
  change (tensor b (tensor (a + a') c)
    = tensor b (tensor a c) + tensor b (tensor a' c)). 
  rhs_V nrapply tensor_dist_l.
  nrapply (ap (tensor b)).
  nrapply tensor_dist_r.
Defined.

(** Given a triple tensor product, we have a twist map which permutes the first two components. *)
Definition ab_tensor_prod_twist {A B C}
  : ab_tensor_prod A (ab_tensor_prod B C) $-> ab_tensor_prod B (ab_tensor_prod A C).
Proof.
  snrapply ab_tensor_prod_rec'.
  - exact ab_tensor_prod_twist_map. 
  - exact ab_tensor_prod_twist_map_additive_l.
Defined.

(** The twist map is involutive. *)
Definition ab_tensor_prod_twist_twist {A B C}
  : ab_tensor_prod_twist $o @ab_tensor_prod_twist A B C $== Id _.
Proof.
  snrapply ab_tensor_prod_ind_homotopy_triple.
  reflexivity.
Defined.

(** The twist map is natural in all 3 arguments. This means that the twist map acts on the triple tensor functor in the same way. *)
Definition ab_tensor_prod_twist_natural {A B C A' B' C'}
  (f : A $-> A') (g : B $-> B') (h : C $-> C')
  : ab_tensor_prod_twist $o fmap11 ab_tensor_prod f (fmap11 ab_tensor_prod g h)
    $== fmap11 ab_tensor_prod g (fmap11 ab_tensor_prod f h) $o ab_tensor_prod_twist.
Proof.
  snrapply ab_tensor_prod_ind_homotopy_triple.
  intros a b c.
  (* This [change] speeds up the [reflexivity].  [simpl] produces a goal that looks the same, but is still slow. *)
  change (tensor (g b) (tensor (f a) (h c)) = tensor (g b) (tensor (f a) (h c))).
  reflexivity.
Defined.

(** ** Unitality of [abgroup_Z] *)

(** In the symmetric monoidal structure on abelian groups, [abgroup_Z] is the unit. We show that tensoring with [abgroup_Z] on the right is isomorphic to the original group. *)

(** First we characterise the action of integers via [grp_pow] and their interaction on tensors. This is just a generalisation of the distributivity laws for tensors. *)

(** Multiplication in the first factor can be factored out. *)
Definition tensor_ab_mul_l {A B : AbGroup} (z : Int) (a : A) (b : B)
  : tensor (ab_mul z a) b = ab_mul z (tensor a b)
  := ab_mul_natural (grp_homo_tensor_r b) z a.

(** Multiplication in the second factor can be factored out. *)
Definition tensor_ab_mul_r {A B : AbGroup} (z : Int) (a : A) (b : B)
  : tensor a (ab_mul z b) = ab_mul z (tensor a b)
  := ab_mul_natural (grp_homo_tensor_l a) z b.

(** Multiplication can be transferred from one factor to the other. The tensor product of [R]-modules will include this as an extra axiom, but here we have [Z]-modules and we can prove it. *)
Definition tensor_ab_mul {A B : AbGroup} (z : Int) (a : A) (b : B)
  : tensor (ab_mul z a) b = tensor a (ab_mul z b).
Proof.
  rhs nrapply tensor_ab_mul_r.
  nrapply tensor_ab_mul_l.
Defined.

(** [abgroup_Z] is a right identity for the tensor product. *) 
Definition ab_tensor_prod_Z_r {A}
  : ab_tensor_prod A abgroup_Z $<~> A.
Proof.
  (** Checking that the inverse map is a homomorphism is easier. *)
  symmetry.
  snrapply Build_GroupIsomorphism.
  - nrapply grp_homo_tensor_r.
    exact 1%int.
  - snrapply isequiv_adjointify.
    + snrapply ab_tensor_prod_rec'.
      * exact grp_pow_homo.
      * intros a a' z; cbn beta.
        nrapply (grp_homo_op (ab_mul z)).
    + hnf.
      change (forall x : ?A, (grp_homo_map ?f) ((grp_homo_map ?g) x) = x)
        with (f $o g $== Id _).
      snrapply ab_tensor_prod_ind_homotopy.
      intros a z.
      change (tensor (B:=abgroup_Z) (grp_pow a z) 1%int = tensor a z).
      lhs nrapply tensor_ab_mul.
      nrapply ap.
      lhs nrapply abgroup_Z_ab_mul.
      apply int_mul_1_r.
    + exact grp_unit_r.
Defined.

(** We have a right unitor for the tensor product given by unit [abgroup_Z]. Naturality of [ab_tensor_prod_Z_r] is straightforward to prove. *)
Global Instance rightunitor_ab_tensor_prod
  : RightUnitor ab_tensor_prod abgroup_Z.
Proof.
  snrapply Build_NatEquiv.
  - intros A.
    apply ab_tensor_prod_Z_r.
  - snrapply Build_Is1Natural.
    intros A A' f.
    snrapply ab_tensor_prod_ind_homotopy.
    intros a z; symmetry.
    exact (grp_pow_natural _ _ _).
Defined.

(** Since we have symmetry of the tensor product, we get left unitality for free. *)
Global Instance left_unitor_ab_tensor_prod
  : LeftUnitor ab_tensor_prod abgroup_Z.
Proof.
  rapply left_unitor_twist.
Defined.

(** ** Symmetric Monoidal Structure of Tensor Product *)

(** Using the twist construction we can derive an associator for the tensor product. In other words, we have associativity of the tensor product of abelian groups natural in each factor. *)
Global Instance associator_ab_tensor_prod : Associator ab_tensor_prod.
Proof.
  srapply associator_twist.
  - exact @ab_tensor_prod_twist.
  - intros; nrapply ab_tensor_prod_twist_twist.
  - intros; nrapply ab_tensor_prod_twist_natural.
Defined.

(** The triangle identity is straightforward to prove using the custom induction principles we proved earlier. *)
Global Instance triangle_ab_tensor_prod
  : TriangleIdentity ab_tensor_prod abgroup_Z.
Proof.
  snrapply triangle_twist.
  intros A B.
  snrapply ab_tensor_prod_ind_homotopy_triple.
  intros a b z; symmetry.
  exact (tensor_ab_mul z a b).
Defined.

(** The hexagon identity is also straighforward to prove. We simply have to reduce all the involved functions on the simple tensors using our custom triple tensor induction principle. *)
Global Instance hexagon_ab_tensor_prod : HexagonIdentity ab_tensor_prod.
Proof.
  snrapply hexagon_twist.
  intros A B C.
  snrapply ab_tensor_prod_ind_homotopy_triple.
  intros b a c.
  change (tensor c (tensor a b) = tensor c (tensor a b)).
  reflexivity.
Defined.

(** Finally, we can prove the pentagon identity using the quadruple tensor induction principle. As we did before, the work only involves reducing the involved functions on the simple tensor redexes. *)
Global Instance pentagon_ab_tensor_prod : PentagonIdentity ab_tensor_prod.
Proof.
  snrapply pentagon_twist.
  intros A B C D.
  snrapply ab_tensor_prod_ind_homotopy_quad.
  intros a b c d.
  change (tensor c (tensor d (tensor a b)) = tensor c (tensor d (tensor a b))). 
  reflexivity.
Defined.

(** We therefore have all the data of a monoidal category. *)
Global Instance ismonoidal_ab_tensor_prod
  : IsMonoidal AbGroup ab_tensor_prod abgroup_Z
  := {}.

(** And furthermore, all the data of a symmetric monoidal category. *)
Global Instance issymmmetricmonoidal_ab_tensor_prod
  : IsSymmetricMonoidal AbGroup ab_tensor_prod abgroup_Z
  := {}.

(** ** Preservation of Coequalizers *)

(** The tensor product of abelian groups preserves coequalizers, meaning that the coequalizer of two tensored groups is the tensor of the coequalizer. We show this is the case on the left and the right. *)

(** Tensor products preserve coequalizers on the right. *)
Definition grp_iso_ab_tensor_prod_coeq_l A {B C} (f g : B $-> C)
  : ab_coeq (fmap01 ab_tensor_prod A f) (fmap01 ab_tensor_prod A g)
    $<~> ab_tensor_prod A (ab_coeq f g).
Proof.
  snrapply cate_adjointify.
  - snrapply ab_coeq_rec.
    + rapply (fmap01 ab_tensor_prod A).
      nrapply ab_coeq_in.
    + refine (_^$ $@ fmap02 ab_tensor_prod _ _ $@ _).
      1,3: rapply fmap01_comp.
      nrapply ab_coeq_glue.
  - snrapply ab_tensor_prod_rec'.
    + intros a.
      snrapply functor_ab_coeq.
      1,2: snrapply (grp_homo_tensor_l a).
      1,2: hnf; reflexivity.
    + intros a a'; cbn beta.
      srapply ab_coeq_ind_hprop.
      intros x.
      exact (ap (ab_coeq_in
        (f:=fmap01 ab_tensor_prod A f)
        (g:=fmap01 ab_tensor_prod A g))
        (tensor_dist_r a a' x)).
  - snrapply ab_tensor_prod_ind_homotopy.
    intros a.
    srapply ab_coeq_ind_hprop.
    intros c.
    reflexivity.
  - snrapply ab_coeq_ind_homotopy.
    snrapply ab_tensor_prod_ind_homotopy.
    reflexivity.
Defined.

(** The equivalence respects the natural maps from [ab_tensor_prod A C]. *)
Definition ab_tensor_prod_coeq_l_triangle A {B C} (f g : B $-> C)
  : grp_iso_ab_tensor_prod_coeq_l A f g $o ab_coeq_in
    $== fmap01 ab_tensor_prod A ab_coeq_in.
Proof.
  snrapply ab_tensor_prod_ind_homotopy.
  reflexivity.
Defined.

(** Tensor products preserve coequalizers on the left. *)
Definition grp_iso_ab_tensor_prod_coeq_r {A B} (f g : A $-> B) C
  : ab_coeq (fmap10 ab_tensor_prod f C) (fmap10 ab_tensor_prod g C)
    $<~> ab_tensor_prod (ab_coeq f g) C.
Proof.
  refine (braide _ _ $oE _).
  nrefine (grp_iso_ab_tensor_prod_coeq_l _ f g $oE _).
  snrapply grp_iso_ab_coeq.
  1,2: rapply braide.
  1,2: symmetry; nrapply ab_tensor_swap_natural.
Defined.

(** The equivalence respects the natural maps from [ab_tensor_prod B C]. *)
Definition ab_tensor_prod_coeq_r_triangle {A B} (f g : A $-> B) C
  : grp_iso_ab_tensor_prod_coeq_r f g C $o ab_coeq_in
    $== fmap10 ab_tensor_prod ab_coeq_in C.
Proof.
  snrapply ab_tensor_prod_ind_homotopy.
  reflexivity.
Defined.

(** ** Tensor Product of Free Abelian Groups *)

Definition equiv_ab_tensor_prod_freeabgroup X Y
  : FreeAbGroup (X * Y) $<~> ab_tensor_prod (FreeAbGroup X) (FreeAbGroup Y).
Proof.
  srefine (let f:=_ in let g:=_ in cate_adjointify f g _ _).
  - snrapply FreeAbGroup_rec.
    intros [x y].
    exact (tensor (freeabgroup_in x) (freeabgroup_in y)).
  - snrapply ab_tensor_prod_rec.
    + intros x.
      snrapply FreeAbGroup_rec.
      intros y; revert x.
      unfold FreeAbGroup.
      snrapply FreeAbGroup_rec.
      intros x.
      apply abel_unit.
      apply freegroup_in.
      exact (x, y).
    + intros x y y'.
      snrapply grp_homo_op.
    + intros x x'.
      rapply Abel_ind_hprop.
      snrapply (FreeGroup_ind_homotopy _ (f' := sgop_hom _ _)).
      intros y.
      lhs nrapply FreeGroup_rec_beta.
      lhs nrapply grp_homo_op.
      snrapply (ap011 (+) _^ _^).
      1,2: nrapply FreeGroup_rec_beta.
  - snrapply ab_tensor_prod_ind_homotopy.
    intros x.
    change (f $o g $o grp_homo_tensor_l x $== grp_homo_tensor_l x).
    rapply Abel_ind_hprop.
    change (@abel_in ?G) with (grp_homo_map (@abel_unit G)).
    repeat change (cat_comp (A:=AbGroup) ?f ?g) with (cat_comp (A:=Group) f g).
    change (forall y, grp_homo_map ?f (abel_unit y) = grp_homo_map ?g (abel_unit y))
      with (cat_comp (A:=Group) f abel_unit $== cat_comp (A:=Group) g abel_unit).
    rapply FreeGroup_ind_homotopy.
    intros y; revert x.
    change (f $o g $o grp_homo_tensor_r (freeabgroup_in y) $== grp_homo_tensor_r (freeabgroup_in y)).
    rapply Abel_ind_hprop.
    change (@abel_in ?G) with (grp_homo_map (@abel_unit G)).
    repeat change (cat_comp (A:=AbGroup) ?f ?g) with (cat_comp (A:=Group) f g).
    change (forall y, grp_homo_map ?f (abel_unit y) = grp_homo_map ?g (abel_unit y))
      with (cat_comp (A:=Group) f abel_unit $== cat_comp (A:=Group) g abel_unit).
    rapply FreeGroup_ind_homotopy.
    intros x.
    reflexivity.
  - rapply Abel_ind_hprop.
    change (GpdHom (A:=Hom(A:=Group) (FreeGroup (X * Y)) _)
      (cat_comp (A:=Group) (g $o f) (@abel_unit (FreeGroup (X * Y))))
      (@abel_unit (FreeGroup (X * Y)))).
    snrapply FreeGroup_ind_homotopy.
    reflexivity.
Defined.

(** ** Tensor products distribute over direct sums *)

Definition ab_tensor_prod_dist_l {A B C : AbGroup}
  : ab_tensor_prod A (ab_biprod B C)
    $<~> ab_biprod (ab_tensor_prod A B) (ab_tensor_prod A C).
Proof.
  srapply (let f := _ in let g := _ in cate_adjointify f g _ _).
  - snrapply ab_tensor_prod_rec.
    + intros a bc.
      exact (tensor a (fst bc), tensor a (snd bc)).
    + intros a bc bc'; cbn beta.
      snrapply path_prod'; snrapply tensor_dist_l.
    + intros a a' bc; cbn beta.
      snrapply path_prod; snrapply tensor_dist_r.
  - snrapply ab_biprod_rec.
    + exact (fmap01 ab_tensor_prod A ab_biprod_inl).
    + exact (fmap01 ab_tensor_prod A ab_biprod_inr).
  - snrapply ab_biprod_ind_homotopy.
    + refine (cat_assoc _ _ _ $@ (_ $@L _) $@ _). 
      1: snrapply ab_biprod_rec_beta_inl.
      snrapply ab_tensor_prod_ind_homotopy.
      intros a b.
      snrapply path_prod; simpl.
      * reflexivity.
      * snrapply tensor_zero_r.
    + refine (cat_assoc _ _ _ $@ (_ $@L _) $@ _).
      1: snrapply ab_biprod_rec_beta_inr.
      snrapply ab_tensor_prod_ind_homotopy.
      intros a b.
      snrapply path_prod; simpl.
      * snrapply tensor_zero_r.
      * reflexivity.
  - snrapply ab_tensor_prod_ind_homotopy.
    intros a [b c].
    lhs_V nrapply tensor_dist_l; simpl.
    snrapply ap.
    symmetry; apply grp_prod_decompose.
Defined.

Definition ab_tensor_prod_dist_r {A B C : AbGroup}
  : ab_tensor_prod (ab_biprod A B) C
    $<~> ab_biprod (ab_tensor_prod A C) (ab_tensor_prod B C).
Proof.
  refine (emap11 ab_biprod (braide _ _) (braide _ _)
    $oE _ $oE braide _ _).
  snrapply ab_tensor_prod_dist_l.
Defined.

(** TODO: Show that the category of abelian groups is symmetric closed and therefore we have adjoint pair with the tensor and internal hom. This should allow us to prove lemmas such as tensors distributing over coproducts. *)
