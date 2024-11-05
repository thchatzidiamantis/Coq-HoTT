Require Import Basics Types.
Require Import Truncations.Core.
Require Import Spaces.Nat.Core.
Require Import Sequences.

Open Scope nat_scope.
Open Scope type_scope.

Definition nat_seq (n : nat) := { i : nat & i < n}.

(** The type of sequences of length [n] with values in [A]. *)
Definition Seq (A : Type) (n : nat) := nat_seq n -> A.
(** Alternate approach:
Definition Seq (A : Type) (n : nat) := (forall (i : nat), i < n -> A). *)

(** Add [a] to the end of the sequence. *)
Definition append {A : Type} {n : nat} (s : Seq A n) (a : A)
  : Seq A n.+1.
Proof.
  intros [i H].
  destruct (dec (i < n)).
  - exact (s (i; l)).
  - exact a.
Defined.

(** Restrict an infinite sequence to be a finite sequence. *)
Definition restrict {A : Type} (s : nat -> A) (n : nat) : Seq A n
  := fun '(i; h) => s i.

(** The empty sequence. *)
Definition seq_nil (A : Type) : Seq A 0.
Proof.
  intros [i H].
  contradiction (not_lt_zero_r i).
Defined.

(** We are not using this definition yet, as it clashes with the implicit {n : nat} in our predicate.  *)
Definition is_bar {A : Type} (B : forall {n : nat} (s : Seq A n), Type)
  := forall (s : nat -> A), {n : nat & B (restrict s n)}.

Definition decidable_bar_induction (A : Type) :=
  forall (B : forall {n : nat} (s : Seq A n), Type)
(* jdc: isprop would be better.  "pred" is often used for predecessor. *)
  (ispred : forall {n : nat} (s : Seq A n), IsHProp (B s))
  (dec : forall {n : nat} (s : Seq A n), Decidable (B s))
  (ind : forall (n : nat) (s : Seq A n), (forall (a : A), B (append s a)) -> B s)
  (bar : forall (s : nat -> A), {n : nat & B (restrict s n)}),
  B (seq_nil A).

(** The statement that the type [A] satisfies bar induction. *)
Definition bar_induction (A : Type) :=
  forall (B : forall {n : nat} (s : Seq A n), Type)
  (ispred : forall {n : nat} (s : Seq A n), IsHProp (B s))
  (ind : forall (n : nat) (s : Seq A n), (forall (a : A), B (append s a)) -> B s)
  (bar : forall (s : nat -> A), {n : nat & B (restrict s n)}),
  B (seq_nil A).  

Definition decidable_fan_theorem (A : Type) :=
  forall (B : forall {n : nat} (s : Seq A n), Type)
  (ispred : forall {n : nat} (s : Seq A n), IsHProp (B s))
  (dec : forall {n : nat} (s : Seq A n), Decidable (B s))
  (bar : forall (s : nat -> A), {n : nat & B (restrict s n)}),
  {M : nat & forall (s : nat -> A), {n : (nat_seq M) & B (restrict s n.1)}}.

Definition fan_theorem (A : Type) :=
  forall (B : forall {n : nat} (s : Seq A n), Type)
  (bar : forall (s : nat -> A), {n : nat & B (restrict s n)}),
  {M : nat & forall (s : nat -> A), {n : (nat_seq M) & B (restrict s n.1)}}.

(** The family we use to apply the fan theorem in our proof that continuity implies uniform continuity *)
Definition uq_theorem_family {A : Type} (p : (nat -> A) -> Bool) 
  : forall (n : nat) (s : Seq A n), Type.
Proof.
  intros n s.
  exact (forall (u v : nat -> A) (h : restrict u n = s), u =[n] v -> p u = p v).
Defined.

Definition is_bar_uq_theorem_family {A : Type} 
  (p : (nat -> A) -> Bool) (conn : is_continuous p)
  : forall (s : nat -> A), {n : nat & uq_theorem_family p n (restrict s n)}.
Proof.
  intro s.
  specialize (conn s 1).
  exists conn.1.
  unfold uq_theorem_family.
  intros u v h.
  assert (d : u =[conn.1] s).
  - (* Incomplete step, searching for the best way to go between =[n] and restrict. 
       Ideally want a theorem (u =[n] v) <-> (restrict u n = restrict v n). *)
    admit. (* jdc: this line need to allow the file to build *)
  - intro t.
    set (l := us_symmetric conn.1 _ _ d).
    set (l' := us_transitive conn.1 _ _ _ l t).
    exact ((conn.2 _ l)^ @ (conn.2 _ l')).
Admitted.  

(** The fan theorem implies that every continuous function is uniformly continuous.
Current proof uses the full fan theorem and is incomplete. Less powerful versions might be enough, e.g. a fan theorem for predicates of type forall {n : nat} (s : Seq A n), Bool *)
Definition uq_theorem (fan : fan_theorem Bool) 
  (p : (nat -> Bool) -> Bool) (conn : is_continuous p)
  : is_uniformly_continuous p.
Proof.
  set (fanapp := fan (uq_theorem_family p) (is_bar_uq_theorem_family p conn)).
  exists fanapp.1.
  intros u v h.
  set (c := conn u).
  set (d := fanapp.2 u) ; set (m := d.1.1) ; set (hm := d.1.2 ) ; set (e := d.2).
  simpl in hm, e.
  unfold uq_theorem_family in e.
  apply e.
  - reflexivity.
  - (* Incomplete step (similar to the one above), follows from h and hm. *)
Admitted.  
