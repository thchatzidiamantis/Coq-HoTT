Require Import Basics Types.
Require Import Truncations.Core.
Require Import Spaces.Nat.Core.
Require Import Spaces.Cantor.
Require Import NatSeq.
Require Import Modalities.ReflectiveSubuniverse.
Require Import Truncations.Connectedness.
Require Import Homotopy.Suspension.
Require Import Pointed.
Require Import Universes.TruncType Universes.HProp.

Open Scope nat_scope.
Open Scope pointed_scope.

(* Is there a propext axiom in the library? *)
Definition hprop_nn_unit_or_empty `{Univalence} (P : HProp) : ~ ((P <> Unit_hp) * (P <> False_hp)).
Proof.
  intros [h1 h2].
  apply (iff_contradiction (~ P)); constructor.
  - intro p.
    exact (h1 (equiv_path_iff_hprop (fun _ => tt, fun _ => p))).
  - intro q.
    exact (h2 (equiv_path_iff_hprop (q, Empty_rec))).
Defined.