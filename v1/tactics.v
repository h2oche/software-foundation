Set Warnings "-notation-overridden,-parsing".
From LF Require Export poly.
(* Export NatList. *)

(* apply tactic *)
Theorem silly1 : forall (n m o p : nat),
     n = m ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  (* rewrite eq2. reflexivity. *)
  apply eq2.
Qed.

(* the universal variable q in eq2
gets instantiated withn and r gets instantiated with m *)

Theorem silly2 : forall (n m o p : nat),
     n = m ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. Qed.

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m) ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.

(* Exercise : silly_ex *)
(* without simpl *)

Lemma modus_ponens:
  forall p q : Prop, (p -> q) -> p -> q.
Proof.
  intros.
  apply H.
  assumption.
Qed.

Lemma modus_ponens_again:
  forall p q : Prop, (p -> q) -> p -> q.
Proof.
  intros.
  apply H in H0.
  assumption.
Qed.

(* Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end. *)
(* Definition oddb (n:nat) : bool := negb (evenb n). *)
Theorem silly_ex :
    (* oddb (S n) = negb evenb n = negb evenb (pred (pred n)) = ... *)
    (forall n, evenb n = true -> oddb (S n) = true) ->
    (* forall n, evenb n = true -> negb evenb (S n) = true *)
    oddb 3 = true ->
    (* negb evenb 3 = true *)
    evenb 4 = true.
    (* evenb 4 = true *)
Proof.
  (* p -> q, ~p? *)
  (* evenb  *)
  intros eq1 eq2.
  (* apply eq1. *)
  (* apply eq1 to eq2 *)
  (* apply eq2. -> why works? *)
  apply eq2.
Qed.

(* To use the apply tactic, the (conclusion of the) fact
being applied must match the goal exactly *)
Theorem silly3_firsttry : forall (n : nat),
     true = (n =? 5) ->
     (S (S n)) =? 7 = true.
Proof.
  intros n H.
  (* apply H. *)
  symmetry.
  simpl.
  apply H.
Qed.

(* Exercise : apply_exercise1 *)
(* Search rev. *)
Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  (* intros.
  rewrite -> H.
  symmetry.
  rewrite rev_involutive.
  reflexivity. -> works *)
  intros.
  rewrite -> H.
  symmetry.
  apply rev_involutive.
Qed.

(* Exercise : apply rewrite *)
(* What is difference?
- rewrite tactic changes expression of goal
  - need additional confirmation tactic like reflexivity
- apply tactic confirms or transforms the goal using environment *)

(* apply with tactic *)

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity. Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  (* by matching the goal against the conclusion of the lemma
   Coq instantiate X with [nat], n with [a,b], and o with [e,f].
   However, the matching process doesn't determine an instantiation for m *)
  apply trans_eq with (m:=[c;d]).
  (* apply trans_eq with [c;d]. also works *)
  apply eq1.
  apply eq2.
Qed.

(* Exercise : apply with exercise *)
Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros.
  apply trans_eq with (m:=m).
  apply H0. apply H.
Qed.

(* Injection, Discriminate tactic *)

(* S is injective ( if S n = S m then n = m)
O, S is disjoint ( O is not same to any S n) *)

(* Inductive nat : Type :=
  | O : nat
  | S : nat -> nat. *)

(* This technique can be generalized to any constructor
by writing the equivalent of pred for that constructor —
i.e., writing a function that "undoes" one application of the constructor *)

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2. rewrite H1. reflexivity.
Qed.

(* using injective tactic *)
Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H.
  intros Hnm.
  apply Hnm.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  injection H. intros H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

Theorem injection_ex2 : forall (n m : nat),
  [n] = [m] ->
  n = m.
Proof.
  intros.
  injection H.
  intros.
  apply H0.
Qed.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  intros.
  injection H0.
  intros.
  symmetry. apply H2.
Qed.

(* The principle of disjointness says that two terms beginning
with different constructors (like O and S, or true and false)
can never be equal *)

(* If we use discriminate on this hypothesis,
Coq confirms that the subgoal we are working on is impossible
and removes it from further consideration. *)

Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'].
  - simpl. intros. reflexivity.
  - simpl. intros. discriminate.
Qed.

(* principle of explosion, 
which asserts that a contradictory hypothesis entails anything,
even false things! *)

Theorem discriminate_ex1 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. Qed.

Theorem discriminate_ex2 : forall (n m : nat),
  false = true ->
  [n] = [m].
Proof.
  intros n m contra. discriminate contra. Qed.

(* Exercise : discriminate_ex3 *)
Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros.
  discriminate H.
Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.

(* Using tactics on hypothesis *)
Theorem S_inj : forall (n m : nat) (b : bool),
     (S n) =? (S m) = b ->
     n =? m = b.
Proof.
  intros n m b H. simpl in H. apply H. Qed.

(* forward reasoning, backward reasoning *)
(* Forward reasoning starts from what is given
(premises, previously proven theorems) and iteratively draws conclusions
from them until the goal is reached. Backward reasoning starts from
the goal, and iteratively reasons about what would imply the goal,
until premises or previously proven theorems are reached. *)

Theorem silly3' : forall (n : nat),
  (n =? 5 = true -> (S (S n)) =? 7 = true) ->
  true = (n =? 5) ->
  true = ((S (S n)) =? 7).
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H. Qed.

(* Exercise : plus_n_n_injective *)
Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  - intro m. induction m as [| m'].
    + simpl. reflexivity.
    + simpl. intro.
      symmetry in H. rewrite <- plus_n_Sm in H.
      discriminate H.
  - intros. induction m as [| m'].
    + discriminate.
    + simpl in H.
      rewrite <- plus_n_Sm in H.
      symmetry in H.
      rewrite <- plus_n_Sm in H.
      injection H. intro.
      symmetry in H0.
      apply IHn' in H0.
      apply f_equal, H0.
Qed.

(* Varying the induction hypothesis *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(* Trying to carry out this proof by induction on n when m
is already in the context doesn't work because we are then
trying to prove a statement involving every n but just a single m. *)

Theorem double_injective_FAILED : forall n m,
  double n = double m ->
  n = m.
Proof.
intros n m. induction n as [| n'].
- (* n = O *) simpl. intros eq. destruct m as [| m'] eqn:E.
 + (* m = O *) reflexivity.
 + (* m = S m' *) discriminate eq.
- (* n = S n' *) intros eq. destruct m as [| m'] eqn:E.
 + (* m = O *) discriminate eq.
 + (* m = S m' *) apply f_equal.
Abort.

(* When using induction, that we are not trying to prove
something too specific: To prove a property of n and m by induction on n,
it is sometimes important to leave m generic. *)

Theorem double_injective: forall n m,
         double n = double m -> n = m.
Proof.
  intros n.
  induction n as [| n'].
  - intros. destruct m as [| m'] eqn:E.
    + reflexivity.
    + discriminate.
  - intros. destruct m as [| m'] eqn:E.
    + discriminate.
    (* + simpl in H. injection H.
      intro. apply IHn' in H0. apply f_equal.
      apply H0. -> it works *)
    + apply f_equal.
      apply IHn'. injection H as goal. apply goal.
Qed.

(* Exercise : eqb_true *)
Theorem eqb_true : forall n m,
    n =? m = true -> n = m.
Proof.
  intro n. induction n as [| n'].
  - intros. destruct m as [| m'] eqn:E.
    + reflexivity.
    + discriminate.
  - intros. destruct m as [| m'] eqn:E.
    + discriminate.
    + simpl in H. apply IHn' in H. apply f_equal, H.
Qed.

(* The strategy of doing fewer intros before an induction
to obtain a more general IH doesn't always work by itself;
sometimes some rearrangement of quantified variables is needed*)

(* The problem is that, to do induction on m, we must first introduce n *)

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction m as [| m'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
        (* Stuck again here, just like before. *)
Abort.

(* generalize dependent tactic *)

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m.
  (* n and m are both in the context *)
  generalize dependent n.
  (* Now n is back in the goal and we can do induction on
     m and get a sufficiently general IH. *)
  induction m as [| m'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
      apply IHm'. injection eq as goal. apply goal. Qed.

(* 
Theorem eqb_id_true : forall x y,
  eqb_id x y = true -> x = y.
Proof.
  intros [m] [n]. simpl. intros H.
  assert (H' : m = n). { apply eqb_true. apply H. }
  rewrite H'. reflexivity.
Qed. *)

(* Exercise : gen_dep_practice *)

(* Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n =? O with
               | true => Some a
               | false => nth_error l' (pred n)
               end
  end. *)

Fixpoint nth_error {X:Type} (l:list X) (n:nat) : option X :=
  match l with
  | [] => None
  | h :: t => if n =? 0 then Some h else nth_error t (pred n)
  end.

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
  length l = n ->
  nth_error l n = None.
Proof.
  intros.
  generalize dependent n.
  induction l as [| h t].
  - intros. simpl. reflexivity.
  - intros. simpl. destruct n as [| n'] eqn:E.
    + simpl. discriminate.
    + simpl. apply IHt. simpl in H. injection H. intro. apply H0.
Qed.

Definition square n := n * n.
Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.
  unfold square.
  (* rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
    { rewrite mult_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity. *)
Admitted.

(* that tactics like simpl, reflexivity, and apply will often
unfold the definitions of functions automatically when this allows
them to make progress *)

Definition foo (x: nat) := 5.

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl. (* Does nothing! *)
Abort.

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
    - (* n =? 3 = true *) reflexivity.
    - (* n =? 3 = false *) destruct (n =? 5) eqn:E2.
      + (* n =? 5 = true *) reflexivity.
      + (* n =? 5 = false *) reflexivity. Qed.

(* Exercise : combine_split *)

Fixpoint split {X Y : Type} (l : list (X*Y))
  : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
    match split t with
    | (lx, ly) => (x :: lx, y :: ly)
    end
end.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l l1 l2.
Admitted.
(* destructing compound expressions, however, the information
recorded by the eqn: can actually be critical: *)

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

Theorem sillyfun1_odd_FAILED : forall (n : nat),
  sillyfun1 n = true ->
  oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3).
  (* the context does not contain enough information to prove the goal *)
  (* stuck... *)
Abort.

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:Heqe3.
  (* Now we have the same state as at the point where we got
     stuck above, except that the context contains an extra
     equality assumption, which is exactly what we need to
     make progress. *)
    - (* e3 = true *) apply eqb_true in Heqe3.
      rewrite -> Heqe3. reflexivity.
    - (* e3 = false *)
     (* When we come to the second equality test in the body
        of the function we are reasoning about, we can use
        eqn: again in the same way, allowing us to finish the
        proof. *)
      destruct (n =? 5) eqn:Heqe5.
        + (* e5 = true *)
          apply eqb_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        + (* e5 = false *) discriminate eq. Qed.

(* Exercise : destruct_eqn_practice *)
Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros.
  symmetry.
  destruct (f b) eqn:F.
  - destruct b eqn:B.
    + rewrite -> F. rewrite -> F. reflexivity.
    + destruct (f true) eqn:F'.
      * symmetry. apply F'.
      * symmetry. apply F.
  - destruct b eqn:B in F.
    + destruct (f false) eqn:F'.
      * symmetry. apply F.
      * symmetry. apply F'.
    + rewrite -> F. rewrite -> F. reflexivity.
Qed.

(* Additional Exercises *)

(* Exercise : eqb_sym *)
Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.

  (* FILL IN HERE *) Admitted.

(* Exercise : eqb_trans *)
Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  (* FILL IN HERE *) Admitted.

(* Exercise : split_combine *)
Definition split_combine_statement : Prop
  (* (": Prop" means that we are giving a name to a
     logical proposition here.) *)
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
Theorem split_combine : split_combine_statement.
Proof.
(* FILL IN HERE *) Admitted.

(* Exercise : filter_exercise *)
Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  (* FILL IN HERE *) Admitted.

(* Exercise : forall_exists_challenge *)
Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
Example test_forallb_1 : forallb oddb [1;3;5;7;9] = true.
Proof. (* FILL IN HERE *) Admitted.
Example test_forallb_2 : forallb negb [false;false] = true.
Proof. (* FILL IN HERE *) Admitted.
Example test_forallb_3 : forallb evenb [0;2;4;5] = false.
Proof. (* FILL IN HERE *) Admitted.
Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. (* FILL IN HERE *) Admitted.
Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. (* FILL IN HERE *) Admitted.
Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. (* FILL IN HERE *) Admitted.
Example test_existsb_3 : existsb oddb [1;0;0;0;0;3] = true.
Proof. (* FILL IN HERE *) Admitted.
Example test_existsb_4 : existsb evenb [] = false.
Proof. (* FILL IN HERE *) Admitted.
Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof. (* FILL IN HERE *) Admitted.