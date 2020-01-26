Set Warnings "-notation-overridden,-parsing".
From LF Require Export indprop.

(* A binary relation on a set X is a family of propositions
parameterized by two elements of X —

i.e., a proposition about pairs of elements of X. *)

(* the Coq identifier relation will always refer to a binary relation
between some set and itself, whereas the English word "relation" can
refer either to the specific Coq concept or the more general concept
of a relation between any number of possibly different sets *)
Definition relation (X: Type) := X -> X -> Prop.

(* Basic Properties *)

(* partial functions *)
(* A relation R on a set X is a partial function if, for every x,
there is at most one y such that R x y — i.e., R x y1 and R x y2
together imply y1 = y2. *)

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Print next_nat.
Check next_nat : relation nat.

Theorem next_nat_partial_function: partial_function next_nat.
Proof.
  unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1. inversion H2.
  reflexivity.
Qed.

Theorem le_not_a_partial_function :
  ~(partial_function le).
Proof.
  unfold partial_function.
  unfold not.
  intro H.
  assert (0 = 1) as Nonsense. {
    apply H with (x := 0).
    - apply le_n.
    - apply le_S. apply le_n.
  }
  discriminate Nonsense.
Qed.

(* reflexive relations *)
Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.
Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive. intro a. apply le_n.
Qed.

(* transitive relations *)
Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
  transitive le.
Proof.
  unfold transitive.
  intros a b c H1 H2.
  induction H2.
  - assumption.
  - apply le_S. apply IHle.
Qed.

Theorem lt_trans:
  transitive lt.
Proof.
  unfold transitive. unfold lt.
  intros a b c H1 H2.
  assert (S a <= S b). {
    apply le_S. assumption.
  } 
  apply (le_trans (S a) (S b) c).
  - assumption.
  - assumption.
Qed.

(* Exercise : le_trans_hard_way *)
Theorem lt_trans' :
  transitive lt.
Proof.
  (* Prove this by induction on evidence that m is less than o. *)
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
  - apply le_S in Hnm. assumption.
  - apply le_S. assumption.
Qed.

(* Exercise : lt_trans'' *)
Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
  - inversion Hmo.
  - inversion Hmo.
    + apply le_S. rewrite H0 in Hnm. assumption.
    + apply le_S. apply IHo'. apply H0.
Qed.

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros.
  Show Proof.
  apply le_trans with (S n).
  Show Proof.
  - apply le_S. apply le_n.
  - Show Proof. apply H.
Qed.

(* Exercise : le_S_n *)
Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  intros n m H.
  inversion H.
  - apply le_n.
  - apply le_Sn_le. assumption.
Qed.

(* Exercise : le_Sn_n *)
Theorem le_Sn_n : forall n,
  ~(S n <= n).
Proof.
  unfold not. intros n H.
  induction n.
  - inversion H.
  - apply IHn. apply le_S_n in H. assumption.
Qed.

(* Symmetric and Antisymmetric Relations *)
Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

(* Exercise : le_not_symmetric *)
Theorem le_not_symmetric :
  ~(symmetric le).
Proof.
  unfold not. unfold symmetric.
  assert (1<=0 -> False) as contra.
  { intro H. inversion H. }
  intros H. 
  apply contra.
  apply H with (a:=0)(b:=1). apply le_S. apply le_n.
Qed.

(* if the only "cycles" in R are trivial ones. *)
Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

(* Exercise : le_antisymmetric *)

Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  unfold antisymmetric.
  intros a b H1 H2.
  induction H2.
  - reflexivity.
  - assert (S m <= m) as contra.
  { apply (le_trans (S m) b m H1 H2). }
  apply le_Sn_n in contra. destruct contra.
Qed.


(* Exercise : le_step *)
Theorem le_step : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
Proof.
  unfold lt. intros n m p Hnm Hmp.
  - assert (S n <= S p). {
    apply (le_trans (S n) m (S p) Hnm Hmp).
  }
    apply le_S_n. assumption.
Qed.

(* Equivalence Relations *)
Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

(* Partial Orders and Preorders *)
(* A relation is a partial order when it's reflexive, anti-symmetric,
and transitive.
In the Coq standard library it's called just "order" for short. *)
Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

(* A preorder is almost like a partial order, but doesn't have to
be antisymmetric. *)
Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).

Theorem le_order :
  order le.
Proof.
  unfold order. split.
  - apply le_reflexive.
  - split.
    + apply le_antisymmetric.
    + apply le_trans.
Qed.

(* Reflexive, Transitive Closure *)

(* The reflexive, transitive closure of a relation R is the smallest
relation that contains R and that is both reflexive and transitive *)
Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
| rt_step x y (H : R x y) : clos_refl_trans R x y
| rt_refl x : clos_refl_trans R x x
| rt_trans x y z
    (Hxy : clos_refl_trans R x y)
    (Hyz : clos_refl_trans R y z) :
    clos_refl_trans R x z.

Theorem next_nat_closure_is_le : forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
intros n m. split.
- (* -> *)
  intro H. induction H.
  + (* le_n *) apply rt_refl.
  + (* le_S *)
    apply rt_trans with m. apply IHle. apply rt_step.
    apply nn.
- (* <- *)
  intro H. induction H.
  + (* rt_step *) inversion H. apply le_S. apply le_n.
  + (* rt_refl *) apply le_n.
  + (* rt_trans *)
    apply le_trans with y.
    apply IHclos_refl_trans1.
    apply IHclos_refl_trans2. Qed.

(* The above definition of reflexive, transitive closure is natural:
it says, explicitly, that the reflexive and transitive closure of R
is the least relation that includes R and that is closed under rules
of reflexivity and transitivity. But it turns out that this definition
is not very convenient for doing proofs, since the "nondeterminism"
of the rt_trans rule can sometimes lead to tricky inductions.

Here is a more useful definition:

Our new definition of reflexive, transitive closure "bundles"
the rt_step and rt_trans rules into the single rule step. The left-hand
premise of this step is a single use of R, leading to a much simpler
induction principle.*)

Inductive clos_refl_trans_1n {A : Type}
                              (R : relation A) (x : A)
                              : A -> Prop :=
  | rt1n_refl : clos_refl_trans_1n R x x
  | rt1n_trans (y z : A)
      (Hxy : R x y) (Hrest : clos_refl_trans_1n R y z) :
      clos_refl_trans_1n R x z.


Lemma rsc_R : forall (X:Type) (R:relation X) (x y : X),
  R x y -> clos_refl_trans_1n R x y.
Proof.
  intros X R x y H.
  apply rt1n_trans with y.
  - assumption.
  - apply rt1n_refl.
Qed.

(* Exercise : rsc_trans *)
Lemma rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      clos_refl_trans_1n R x y ->
      clos_refl_trans_1n R y z ->
      clos_refl_trans_1n R x z.
Proof.
  intros X R x y z H1 H2.
  induction H1.
  - assumption.
  - apply rt1n_trans with y.
    + assumption.
    + apply IHclos_refl_trans_1n. apply H2.
Qed.

(* Exercise : rtc_rsc_coincide *)
Theorem rtc_rsc_coincide : forall (X:Type) (R: relation X) (x y : X),
  clos_refl_trans R x y <-> clos_refl_trans_1n R x y.
Proof.
  intros X R x y. split.
  - intro H. induction H.
    + apply rt1n_trans with y.
      * assumption.
      * apply rt1n_refl.
    + apply rt1n_refl.
    + apply rsc_trans with y. assumption. assumption.
  - intro H. induction H.
    + apply rt_refl.
    + apply rt_trans with y.
      * apply rt_step. apply Hxy.
      * apply IHclos_refl_trans_1n.
Qed.

