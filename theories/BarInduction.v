Require Import Basics Types.
Require Import Truncations.Core.
Require Import Spaces.Nat.Core.
Require Import Basics Types.
Require Import Truncations.Core.
Require Import Spaces.Nat.Core.
Require Import Spaces.Finite.FinNat Spaces.Finite.FinSeq.
Require Import NatSeq.
Require Import ExcludedMiddle.
Require Import Spaces.List.Core Spaces.List.Paths Spaces.List.Theory.
Require Import Algebra.Rings.Vector.

Open Scope nat_scope.
Open Scope type_scope.
Open Scope list_scope.

(** Want to prove:
- LEM => BI
- Monotone BI => FAN
- BI => LLPO
- FAN Bool <=> is_searchable Cantor

- Lots of rewrites, get rid of them. *)

(** These next two are just the parts that make up Build_Vector. *)
Definition Build_list {A : Type} (n : nat) (f : forall (i : nat), (i < n)%nat -> A)
  : list A
  := list_map (fun '(i; Hi) => f i Hi) (seq' n).

Definition length_Build_list {A : Type} (n : nat)
  (f : forall (i : nat), (i < n)%nat -> A)
  : length (Build_list n f) = n.
Proof.
  lhs nrapply length_list_map.
  apply length_seq'.
Admitted.

(** Converse to path_vector *)
Definition vector_path {A : Type} {n : nat} {v1 v2 : Vector A n}
  (h : v1 = v2) (i : nat) (H : i < n)
  : entry v1 i = entry v2 i
  := match h with idpath => 1 end.

Definition empty_Vector (A : Type) : Vector A 0 := (nil; idpath).

Definition empty_if_length_0 {A : Type} (v : Vector A 0)
  : v = empty_Vector A
  := path_vector _ _ _ (fun i Hi => Empty_rect (fun _ => _) (not_lt_zero_r i Hi)).

Definition Vector_app {A : Type} {m n : nat} (u : Vector A m) (v : Vector A n)
  : Vector A (m + n).
Proof.
  exists (u.1 ++ v.1).
  lhs nrapply length_app.
  exact (ap011 _ u.2 v.2).
Defined.

Definition app_empty_empty (A : Type)
  : Vector_app (empty_Vector A) (empty_Vector A) = empty_Vector A
  := idpath.

(** I cannot do this for w ++ empty, because the lengths don't work definitionally. *)
Definition app_empty {A : Type} {n : nat} (v : Vector A n)
  : Vector_app (empty_Vector A) v = v.
Proof.
  apply path_vector.
  induction n.
  - rewrite (empty_if_length_0 v).
    reflexivity.
  - admit.
Admitted.

Definition term_to_Vector {A : Type} (a : A) : Vector A 1
  := Build_Vector A 1 (fun _ _ => a).

(** Add [a] to the end of the sequence. *)
Definition append {A : Type} {n : nat} (s : Vector A n) (a : A)
  : Vector A (n + 1)
  := Vector_app s (term_to_Vector a).

(** Restrict an infinite sequence to be a finite sequence. *)
Definition restrict {A : Type} (s : nat -> A) (n : nat) : Vector A n
  := Build_Vector A n (fun m _ => s m).

Definition entry_restrict {A : Type} (s : nat -> A) (n : nat) i {Hi : (i < n)%nat}
  : entry (restrict s n) i = s i
  := entry_Build_Vector _ _.

Definition restrict' {A : Type} (s : nat -> A) (n : nat) : list A
  := Build_list n (fun m _ => s m).

Definition restrict'_length {A : Type} (s : nat -> A) (n : nat)
  : length (restrict' s n) = n
  := length_Build_list _ _.

Definition restrict'_length_2 {A : Type} (s t : nat -> A) (n : nat)
  : length (restrict' s n) = length (restrict' t n)
  := (restrict'_length s n) @ (restrict'_length t n)^.

Definition restrict'_length_path {A : Type} (s : nat -> A) {m n : nat} (h : m = n)
  : restrict' s m = restrict' s n
  := match h with idpath => idpath end.

(* This has been copied from vectors, can it be simplified? *)
Definition entry_restrict' {A : Type} (s : nat -> A) (n : nat)
  {i : nat} (Hi : i < n)
  : nth' (restrict' s n) i ((restrict'_length s n)^ # Hi) = s i.
Proof.
  snrefine (nth'_list_map _ _ _ (_^ # Hi) _ @ _).
  - nrapply length_seq'.
  - exact (ap s (nth'_seq' _ _ _)).
Defined.

Definition entry_restrict'_2 {A : Type} (s : nat -> A) (n : nat)
  {i : nat} (Hi : i < length (restrict' s n))
  : nth' (restrict' s n) i Hi = s i.
Proof.
  snrefine (nth'_list_map _ _ _ (_^ # Hi) _ @ _).
  - nrapply ((length_seq' n) @ (restrict'_length s n)^).
  - exact (ap s (nth'_seq' _ _ _)).
Defined.

Definition restrict_eq_iff {A : Type} {n : nat} {u v : nat -> A}
  : (restrict u n = restrict v n) <-> (forall (m : nat), m < n -> u m = v m).
Proof.
  constructor.
  - intros h m hm.
    lhs srapply (entry_restrict u n m)^; rhs srapply (entry_restrict v n m)^.
    destruct h.
    reflexivity.
  - intro h.
    apply path_vector.
    intros i Hi.
    lhs nrapply entry_restrict; rhs nrapply entry_restrict.
    exact (h i Hi).
Defined.

Definition nth'_path_list {A : Type} {l1 l2 : list A}
  (p : l1 = l2) {n : nat} (Hn : n < length l1)
  : nth' l1 n Hn = nth' l2 n ((ap _ p) # Hn)
  := match p with idpath => idpath end.

Definition nth'_path_list' {A : Type} {l1 l2 : list A}
  (p : l1 = l2) {n : nat} (Hn1 : n < length l1) (Hn2 : n < length l2)
  : nth' l1 n Hn1 = nth' l2 n Hn2.
Proof.
  destruct p.
  by apply nth'_nth'.
Defined.

Definition restrict_tail_eq {A : Type} {n : nat} {u v : nat -> A}
  (h : restrict u n.+1 = restrict v n.+1)
  : restrict (NatSeq.tail u) n = restrict (NatSeq.tail v) n.
Proof.
  apply path_vector.
  intros i Hi.
  lhs nrapply entry_restrict; rhs nrapply entry_restrict.
  unfold NatSeq.tail.
  pose (h' := vector_path h i.+1 _).
  (* Get rid of the rewrite. *)
  repeat rewrite entry_restrict in h'.
  exact h'.
Defined.

Definition seq_agree_res {A : Type} {n : nat} {u v : nat -> A}
  (h : restrict u n = restrict v n)
  : u =[n] v.
Proof.
  induction n in u, v, h |-*.
  - exact tt.
  - constructor.
    + unfold NatSeq.head.
      exact (fst (restrict_eq_iff) h 0 _).
    + exact (IHn _ _ (restrict_tail_eq h)).
    (* + rapply (h (0 ; _)).
      exact _.
    + apply IHn.
      intros (k , hk).
      exact (h (k.+1 ; lt_succ hk)). *)
Defined.

(* One place where vectors will be important: Lists of the same length with the same entries are the same. *)
Definition res_seq_agree {A : Type} {n : nat} {u v : nat -> A}
  (h : u =[n] v)
  : restrict u n = restrict v n.
Proof.
  apply path_vector.
  intros i Hi.
  induction n in u, v, h, i, Hi |-*.
  - contradiction (not_lt_zero_r _ Hi).
  (* lemma: restrictions have the same entries in compatible places. *)
  - lhs srapply entry_restrict; rhs srapply entry_restrict; induction i.
    + exact (fst h).
    + pose (ih := IHn (NatSeq.tail u) (NatSeq.tail v) (snd h) i _).
      (* Get rid of the rewrite. *)
      repeat rewrite entry_restrict in ih.
      rapply ih.
  (* intros (m , hm).
  induction n in u, v, m, h, hm |-*.
  - contradiction (not_lt_zero_r _ hm).
  - induction m in u, v, h, hm |-*.
    + exact (fst h).
    + rapply (IHn (tail u) (tail v) (snd h)). *)
Defined.

Definition seq_agree_iff_res {A : Type} {n : nat} {u v : nat -> A}
  : (u =[n] v) <-> restrict u n = restrict v n
  := (fun h => res_seq_agree h, fun h => seq_agree_res h).

Definition restrict_eq_iff' {A : Type} {n : nat} {s t : nat -> A}
  : (restrict' s n = restrict' t n) <-> (forall (m : nat), m < n -> s m = t m).
Proof.
  constructor.
  - intros h m hm.
    lhs srapply (entry_restrict' s n hm)^.
    rhs srapply (entry_restrict' t n hm)^.
    exact (nth'_path_list' h _ _).
  - intro h.
    apply (path_list_nth' _ _ (restrict'_length_2 s t n)).
    intros i Hi.
    lhs srapply (entry_restrict'_2 s n _).
    rhs srapply (entry_restrict'_2 t n _).
    exact (h i ((restrict'_length s n) # Hi)).
Defined.

Definition seq_agree_iff_res' {A : Type} {n : nat} {s t : nat -> A}
  : restrict' s n = restrict' t n <-> (s =[n] t)
  := iff_compose restrict_eq_iff' us_sequense_eq_iff.

Definition is_bar {A : Type} (B : list A -> Type)
  := forall (s : nat -> A), {n : nat & B (restrict' s n)}.

Definition is_uniform_bar {A : Type} (B : list A -> Type)
  := {M : nat & forall (s : nat -> A), {n : (FinNat M) & B (restrict' s n.1)}}.

Definition is_inductive {A : Type} (B : list A -> Type)
  := forall (l : list A), (forall (a : A), B (a::l)) -> B l.

Definition is_monotone {A : Type} (B : forall (l : list A), Type)
  := forall (l1 l2 : list A), B l1 -> B (l1++l2).

Definition decidable_bar_induction (A : Type) :=
  forall (B : list A -> Type)
  (* (isprop : forall {n : nat} (s : Vector A n), IsHProp (B s)) *)
  (dec : forall (l : list A), Decidable (B l))
  (ind : is_inductive B)
  (bar : is_bar B),
  B (nil).

Definition monotone_bar_induction (A : Type) :=
  forall (B : list A -> Type)
  (mon : is_monotone B)
  (ind : is_inductive B)
  (bar : is_bar B),
  B (nil).

Definition monotone_bar_induction' (A : Type) :=
  forall (B C : list A -> Type)
  (sub : forall l : list A, C l -> B l)
  (monC : is_monotone C)
  (indB : is_inductive B)
  (barC : is_bar C),
  B (nil).

(** The statement that the type [A] satisfies bar induction. *)
Definition bar_induction (A : Type) :=
  forall (B : list A -> Type)
  (ind : is_inductive B)
  (bar : is_bar B),
  B (nil).

Definition bar_induction' (A : Type) :=
  forall (B C : list A -> Type)
  (sub : forall l : list A, C l -> B l)
  (indB : is_inductive B)
  (barC : is_bar C),
  B (nil).

Definition bar_induction'_bar_induction (A : Type) (BI : bar_induction A)
  : bar_induction' A
  := fun B C sub indB barC => BI B indB (fun s => ((barC s).1; sub _ (barC s).2)).

Definition monotone_bar_induction_iff (A : Type)
  : monotone_bar_induction A -> monotone_bar_induction' A.
Proof.
  intro BI.
  intros B C sub monC indB barC.
  pose (P := fun v => forall w, B (v++w)).
  assert (barP : is_bar P).
  - intro s; exact ((barC s).1; fun _ => sub _ (monC _ _ (barC s).2)).
  - assert (indP : is_inductive P).
    + exact (fun _ H _ => indB _ (fun a => H a _)).
    + assert (monP : is_monotone P).
      * intros u v H w.
        rewrite <- app_assoc.
        exact (H (v++w)).
      * exact (BI P monP indP barP nil).
Defined.

(*** Bar induction implies bad things. *)

Definition BI_Kleene_family {A : Type} (P : A -> Type) (l : list A)
  : Type
  := match l with
      | nil => Decidable (forall a, P a)
      | n :: l' => (P n) * (length l' = 0)
     end.

Definition is_bar_BI_Kleene_family {A : Type} {P : A -> Type}
  (dec : forall n : A, Decidable (P n))
  : is_bar (BI_Kleene_family P).
Proof.
  intro s.
  destruct (dec (s 0)) as [p|p'].
  - exists 1.
    exact (p, idpath).
  - exists 0.
    rewrite (length_0 _ (restrict'_length s 0)).
    exact (inr (fun (u : forall a, P a) => p' (u (s 0)))).
Defined.

(** Can I get rid of pointedness? *)
Definition is_inductive_BI_Kleene_family {A : pType} (P : A -> Type)
  : is_inductive (BI_Kleene_family P).
Proof.
  intros l h.
  remember (length l) as m eqn:r; induction m.
  - rewrite (length_0 l (snd (h (point A)))).
    exact (inl (fun k => fst (h k))).
  - contradiction (neq_nat_zero_succ m ((snd (h (point A)))^ @ r)).
Defined.

Definition BI_Kleene_family' {A : Type} (P : A -> Type) (l : list A)
  : Type
  := match l with
      | nil => Decidable {a : A & P a}
      | n :: l' => (~(P n)) * (length l' = 0)
     end.

Definition is_bar_BI_Kleene_family' {A : Type} {P : A -> Type}
  (dec : forall n : A, Decidable (P n))
  : is_bar (BI_Kleene_family' P).
Proof.
  intro s.
  destruct (dec (s 0)) as [p|p'].
  - exists 0.
    rewrite (length_0 _ (restrict'_length s 0)).
    exact (inl (s 0; p)).
  - exists 1.
    exact (p', idpath).
Defined.

Definition is_inductive_BI_Kleene_family' {A : pType} (P : A -> Type)
  : is_inductive (BI_Kleene_family' P).
Proof.
  intros l h.
  remember (length l) as m eqn:r; induction m.
  - rewrite (length_0 l (snd (h (point A)))).
    simpl in h; simpl.
    exact (inr (fun k => (fst (h k.1)) k.2)).
  - contradiction (neq_nat_zero_succ m ((snd (h (point A)))^ @ r)).
Defined.

(** Relation to Π-compactness? *)
Definition bar_induction_is_not_good_I_think {A : pType} (BI : bar_induction A)
  {P : A -> Type} (dec : forall n : A, Decidable (P n))
  : Decidable (forall a, P a)
  := BI (BI_Kleene_family P) 
          (is_inductive_BI_Kleene_family P) (is_bar_BI_Kleene_family dec).

Definition bar_induction_is_not_good_I_think' {A : pType} (BI : bar_induction A)
  {P : A -> Type} (dec : forall n : A, Decidable (P n))
  : Decidable {a : A & P a}
  := BI (BI_Kleene_family' P)
          (is_inductive_BI_Kleene_family' P) (is_bar_BI_Kleene_family' dec).

(*** The Fan theorem.  *)

Definition decidable_fan_theorem (A : Type) :=
  forall (B : list A -> Type)
  (* (isprop : forall {n : nat} (s : Vector A n), IsHProp (B s)) *)
  (dec : forall l : list A, Decidable (B l))
  (bar : is_bar B),
  is_uniform_bar B.

Definition monotone_fan_theorem (A : Type) :=
  forall (B : list A -> Type)
  (mon : is_monotone B)
  (bar : is_bar B),
  is_uniform_bar B.

Definition fan_theorem (A : Type) :=
  forall (B : list A -> Type)
  (bar : is_bar B) ,
  is_uniform_bar B.

Definition fan_monotone_fan A (m : monotone_fan_theorem A) : fan_theorem A.
Proof.
  intros B bar.
  unfold is_uniform_bar; unfold is_bar in bar.
Admitted.

Definition fan_bar_family {A : Type} (B : list A -> Type) (l : list A)
  : Type.
Proof.
  induction l.
  - exact (is_uniform_bar B).
  - 
Admitted.

(** The family we use to apply the fan theorem in our proof that continuity implies uniform continuity *)
Definition uq_theorem_family {A : Type} (p : (nat -> A) -> Bool)
  : list A -> Type
  := fun l =>
      (forall (u v : nat -> A) (h : restrict' u (length l) = l), u =[length l] v -> p u = p v).

Definition is_bar_uq_theorem_family {A : Type}
  (p : (nat -> A) -> Bool) (conn : is_continuous p)
  : is_bar (uq_theorem_family p).
Proof.
  intro s.
  specialize (conn s 1).
  exists conn.1.
  unfold uq_theorem_family.
  intros u v h t.
  rewrite (restrict'_length) in h, t.
  pose (y := us_symmetric conn.1 _ _ ((fst seq_agree_iff_res') h)).
  pose (y' := us_transitive conn.1 _ _ _ y t).
  exact ((conn.2 _ y)^ @ (conn.2 _ y')).
Defined.

(** The fan theorem implies that every continuous function is uniformly continuous.
Current proof uses the full fan theorem. Less powerful versions might be enough, e.g. a fan theorem for predicates of type forall {n : nat} (v : Vector A n), Bool 

- Is the converse true? *)

Definition uq_theorem {A : Type} (fan : fan_theorem A)
  (p : (nat -> A) -> Bool) (conn : is_continuous p)
  : is_uniformly_continuous p.
Proof.
  pose (fanapp := fan (uq_theorem_family p) (is_bar_uq_theorem_family p conn)).
  exists fanapp.1.
  intros u v h.
  apply (fanapp.2 u).2.
  - exact (restrict'_length_path _ (restrict'_length _ _)).
  - rewrite restrict'_length.
    exact ((us_rel_leq (_ (fanapp.2 u).1.2) h)).
Defined.