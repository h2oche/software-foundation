Notation "x + y" := (plus x y).
Notation "x - y" := (minus x y).
Notation "x * y" := (mult x y).
Theorem plusN0: forall n:nat, n + 0 = n.
Proof.
  (* intros.
  simpl.
  reflexivity. *)
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem MinusSelf: forall n:nat, n - n = 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mult_0_r : forall n:nat, n * 0 = 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros.
  induction n as [| n' IHn'].
  - simpl. induction m as [| m' IHm'].
    + simpl. reflexivity.
    + simpl. rewrite <- IHm'. reflexivity.
  - simpl. induction m as [| m' IHm'].
    + simpl. rewrite -> plusN0. reflexivity.
    + simpl.
      rewrite -> IHn'.
      simpl.
      rewrite <- plus_n_Sm.
      reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
  intros.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl.
    rewrite -> plus_comm.
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)... seems
     like plus_comm should do the trick! *)
  rewrite -> plus_comm.
  (* Doesn't work...Coq rewrites the wrong plus! *)
Abort.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity. Qed.