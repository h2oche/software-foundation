Set Warnings "-notation-overridden,-parsing".
From LF Require Export proofobj.

(* Basics *)

(* Every time we declare a new Inductive datatype, Coq automatically
generates an induction principle for this type. *)

(* If t is defined inductively, the corresponding induction principle
is called t_ind. Here is the one for natural numbers *)

Check nat_ind.

(* The "induction"s tactic is a straightforward wrapper that,
at its core, simply performs apply t_ind *)

Theorem mult_0_r' : forall n:nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  - (* n = O *) reflexivity.
  - (* n = S n' *) simpl. intros n' IHn'. rewrite -> IHn'.
    reflexivity. Qed.

(* Exercise : plus_one_r' *)

Theorem plus_one_r' : forall n:nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. intros n H. rewrite H. reflexivity.
Qed.

(* Coq generates induction principles for every datatype defined
with Inductive, including those that aren't recursive *)

(* If we define a type t with constructors c1 ... cn,
Coq generates a theorem with this shape:
    t_ind : ∀P : t → Prop,
              ... case for c1 ... →
              ... case for c2 ... → ...
              ... case for cn ... →
              ∀n : t, P n *)

Inductive yesno : Type :=
| yes
| no.

Check yesno_ind.

(* Exercise : rgb *)
Inductive rgb : Type :=
| red
| green
| blue.
Check rgb_ind.

(* Exercise : natlist1 *)
Inductive natlist : Type :=
| nnil
| ncons (n : nat) (l : natlist).
Check natlist_ind.

Inductive natlist1 : Type :=
  | nnil1
  | nsnoc1 (l : natlist1) (n : nat).
Check natlist1_ind.

(*
- The type declaration gives several constructors; each corresponds
  to one clause of the induction principle.
- Each constructor c takes argument types a1 ... an.
- Each ai can be either t (the datatype we are defining)
  or someother type s.
- The corresponding case of the induction principle says:
  "For all values x1...xn of types a1...an, if P holds for each of
  the inductive arguments (each xi of type t),
  then P holds for c x1 ... xn". *)

(* Exercise : byntree_ind *)
Inductive byntree : Type :=
| bempty
| bleaf (yn : yesno)
| nbranch (yn : yesno) (t1 t2 : byntree).
Check byntree_ind.

(* Exercise : ex_set *)
(* 
induction principle for an inductively defined set.  
ExSet_ind :
         ∀P : ExSet → Prop,
             (∀b : bool, P (con1 b)) →
             (∀(n : nat) (e : ExSet), P e → P (con2 n e)) →
             ∀e : ExSet, P e *)

Inductive ExSet : Type :=
| con1 (b: bool)
| con2 (n : nat) (e : ExSet).
Check ExSet_ind.

(* Polymorphism *)
Inductive list (X:Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.
(* whole induction principle is parameterized on X.
That is, list_ind can be thought of as a polymorphic function that,
when applied to a type X, gives us back an induction principle
specialized to the type list X. *)
Check list_ind.

(* Exercise : tree *)
Inductive tree (X:Type) : Type :=
| leaf (x : X)
| node (t1 t2 : tree X).
Check tree_ind.

(* Exercise : mytype *)
(* mytype_ind :
        ∀(X : Type) (P : mytype X → Prop),
            (∀x : X, P (constr1 X x)) →
            (∀n : nat, P (constr2 X n)) →
            (∀m : mytype X, P m →
               ∀n : nat, P (constr3 X m n)) →
            ∀m : mytype X, P m *)
Inductive mytype (X:Type) : Type :=
| constr1(x : X)
| constr2(n : nat)
| constr3(m : mytype X) (n : nat).

(* Exercise : foo *)
(* foo_ind :
        ∀(X Y : Type) (P : foo X Y → Prop),
             (∀x : X, P (bar X Y x)) →
             (∀y : Y, P (baz X Y y)) →
             (∀f1 : nat → foo X Y,
               (∀n : nat, P (f1 n)) → P (quux X Y f1)) →
             ∀f2 : foo X Y, P f2 *)
Inductive foo (X Y : Type) : Type :=
| bar (x : X)
| baz (y : Y)
| quux (f1 : nat -> foo X Y).
Check foo_ind.

(* Induction Hypotheses *)
Definition P_m0r (n:nat) : Prop :=
  n * 0 = 0.

Definition P_m0r' : nat->Prop :=
  fun n => n * 0 = 0.

(* it allows us to see exactly what the induction hypothesis is *)
Theorem mult_0_r'' : forall n:nat,
  P_m0r n.
Proof.
  apply nat_ind.
  - (* n = O *) reflexivity.
  - (* n = S n' *)
    (* Note the proof state at this point! *)
    intros n IHn.
    unfold P_m0r in IHn. unfold P_m0r. simpl. apply IHn. Qed.

(* More on the induction tactic *)

(* when we begin a proof with intros n and then induction n,
we are first telling Coq to consider a particular n (by introducing
it into the context) and then telling it to prove something about
all numbers (by using induction).

What Coq actually does in this situation, internally,
is to "re-generalize" the variable we perform induction on. *)

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  (* ...we first introduce all 3 variables into the context,
     which amounts to saying "Consider an arbitrary n, m, and
     p..." *)
  intros n m p.
  (* ...We now use the induction tactic to prove P n (that
     is, n + (m + p) = (n + m) + p) for _all_ n,
     and hence also for the particular n that is in the context
     at the moment. *)
  induction n as [| n'].
  - (* n = O *) reflexivity.
  - (* n = S n' *)
    (* In the second subgoal generated by induction -- the
       "inductive step" -- we must prove that P n' implies
       P (S n') for all n'.  The induction tactic
       automatically introduces n' and P n' into the context
       for us, leaving just P (S n') as the goal. *)
    simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_comm' : forall n m : nat,
  n + m = m + n.
Proof.
  induction n as [| n'].
  - (* n = O *) intros m. rewrite <- plus_n_O. reflexivity.
  - (* n = S n' *) intros m. simpl. rewrite -> IHn'.
    rewrite <- plus_n_Sm. reflexivity. Qed.

(* If we do induction on a variable that is quantified in the goal
after some other quantifiers, the induction tactic will automatically
introduce the variables bound by these quantifiers into the context. *)

Theorem plus_comm'' : forall n m : nat,
  n + m = m + n.
Proof.
  (* Let's do induction on m this time, instead of n... *)
  induction m as [| m'].
  - (* m = O *) simpl. rewrite <- plus_n_O. reflexivity.
  - (* m = S m' *) simpl. rewrite <- IHm'.
    rewrite <- plus_n_Sm. reflexivity. Qed.

(* Induction Principles in Prop *)

Inductive even : nat -> Prop :=
| ev_0 : even 0
| ev_SS : forall n : nat, even n -> even (S (S n)).

(* Suppose, P is a property of natural numbers (that is, P n is a Prop
for every n). To show that P n holds whenever n is even, it suffices to
show:

- P holds for 0,
- for any n, if n is even and P holds for n, then P holds for S (S n). *)
Check even_ind.

Theorem ev_ev' : forall n, even n -> even' n.
Proof.
  apply even_ind.
  - (* ev_0 *)
    apply even'_0.
  - (* ev_SS *)
    intros m Hm IH.
    apply (even'_sum 2 m).
    + apply even'_2.
    + apply IH.
Qed.

Inductive le (n:nat) : nat -> Prop :=
  | le_n : le n n
  | le_S m (H : le n m) : le n (S m).
Notation "m <= n" := (le m n).