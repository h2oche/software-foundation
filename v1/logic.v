Set Warnings "-notation-overridden,-parsing".
From LF Require Export tactics.
From LF Require Export induction.

(* Indeed, propositions don't just have types:
they are first-class objects that can be manipulated
in the same ways as the other entities in Coq's world. *)

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.

(* parameterized propositions *)
Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.

(* In Coq, functions that return propositions
are said to define properties of their arguments. *)
Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H. injection H as H1. apply H1.
Qed.

(* The equality operator = is also a function that returns a Prop.
= is syntactic sugar of eq *)
Check (forall (X Y : Prop), ( X = Y )).
Check @eq.

(* Logical Connectives *)

(* conjunction *)
(* To prove a conjunction, use the split tactic.
/\ = and *)
Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(* Exercise : and_exercise *)
Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros.
  split.
  - destruct n.
    + reflexivity.
    + discriminate.
  - destruct m as [| m'].
    + reflexivity.
    + rewrite plus_comm in H. simpl in H. discriminate H.
Qed.

(* to use a conjunctive hypothesis to help prove something else
— we employ the destruct tactic *)

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  assert (H' : n = 0 /\ m = 0).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP. Qed.

(* Exercise : prop2 *)
Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q [HP HQ].
  apply HQ. Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP. Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split.
    + apply HP.
    + apply HQ.
  - apply HR.
Qed.

(* Disjunction *)

Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on
     n = 0 ∨ m = 0 *)
  intros n m [Hn | Hm].
  - (* Here, n = 0 *)
    rewrite Hn. reflexivity.
  - (* Here, m = 0 *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  (* WORKED IN CLASS *)
  intros [| n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

(* Falsehood and negation *)

(* Following intuition of principle explosion,
we could define ¬ P ("not P") as forall  Q, P -> Q.
Coq actually makes a slightly different (but equivalent) choice,
defining ¬ P as P -> False
False : contradictory proposition *)

Module MyNot.

Definition not (P:Prop) := P -> False.
Notation "~ x" := (not x) : type_scope.
Check not.
(* ===> Prop -> Prop *)
End MyNot.

(* If we get False into the proof context,
we can use destruct on it to complete any goal *)
Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  destruct contra. Qed.

(* Exercise : not implies our not *)
(* not P is same to P is contra *)
Fact not_implies_our_not : forall (P:Prop),
  ~P -> (forall (Q:Prop), P -> Q).
Proof. intros. apply H in H0. destruct H0. Qed.

Notation "x != y" := (~(x = y)) (at level 50).

Theorem zero_not_one : 0 != 1.
Proof.
  unfold not.
  intros contra.
  discriminate contra.
Qed.

Theorem not_False :
  ~False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP. Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H. Qed.

(* Exercise : contrapositive *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q. unfold not.
  intros H QF PT.
  apply H in PT. apply QF in PT.
  destruct PT.
Qed.

(* Exercise : not both true and false *)
Theorem not_both_true_and_false : forall P : Prop,
  ~(P /\ ~P).
Proof.
  intro P. 
  intros [HP HNP].
  unfold not in HNP.
  apply HNP in HP.
  destruct HP.
Qed.

(* If you are trying to prove a goal that is nonsensical
(e.g., the goal state is false = true), apply ex_falso_quodlibet
to change the goal to False *)

Theorem not_true_is_false : forall b : bool,
  b != true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

(* exfalso tactic *)
Theorem not_true_is_false' : forall b : bool,
  b != true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    exfalso. (* <=== *)
    apply H. reflexivity.
  - (* b = false *) reflexivity.
Qed.

(* truth *)
(* True can be quite useful when defining complex Props
using conditionals or as a parameter to higher-order Props *)
Lemma True_is_true : True.
Proof. apply I. Qed.

(* Logical Equivalence *)

Module MyIff.
Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).
Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.
End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB. Qed.

Lemma not_true_iff_false : forall b,
  b != true <-> b = false.
Proof.
  (* WORKED IN CLASS *)
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. 
    (* unfold not. *)
    intros H'. discriminate H'.
Qed.


(* Exercise : or distributes over and *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  - intros [HP | [HQ HR]].
    + split.
      * left. apply HP.
      * left. apply HP.
    + split.
      * right. apply HQ.
      * right. apply HR.
  - intros [[HP|HQ] [HP'|HR]].
    + left. apply HP.
    + left. apply HP.
    + left. apply HP'.
    + right. split.
      * apply HQ.
      * apply HR.
Qed.

(* Some of Coq's tactics treat iff statements specially,
avoiding the need for some low-level proof-state manipulation.
In particular, rewrite and reflexivity can be used with iff statements,
not just equalities *)
From Coq Require Import Setoids.Setoid.

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
Admitted.

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.
(* Search mult. *)
Lemma mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc.
  reflexivity.
Qed.

(* The apply tactic can also be used with <-> *)
Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. apply H.
Qed.

(* Existential Quantification *)

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  (* WORKED IN CLASS *)
  intros n [m Hm]. (* note implicit destruct here *)
  exists (2 + m).
  apply Hm. Qed.

(* Exercise : does not exist *)
Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~(exists x, ~P x).
Proof.
  intros.
  unfold not.
  intros [x Hx].
  apply Hx.
  apply H.
Qed.

(* Exercise : dist exists or *)
Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros.
  split.
  - intros [x [HPX | HQX]].
    + left. exists x. apply HPX.
    + right. exists x. apply HQX.
  - intros [[x HPX] | [x HQX]].
    + exists x. left. apply HPX.
    + exists x. right. apply HQX.
Qed.

(* Programming with Propositions *)

(* list l contains x? *)
Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  (* WORKED IN CLASS *)
  simpl. right. right. right. left. reflexivity.
Qed.

(* use of the empty pattern to discharge the last case en passant. *)
Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  (* WORKED IN CLASS *)
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

(* This way of defining propositions recursively,
though convenient in some cases, also has some drawbacks.
In particular, it is subject to Coq's usual restrictions
regarding the definition of recursive functions,
e.g., the requirement that they be "obviously terminating." *)

Theorem and_distributes_over_or : forall P Q R : Prop,
  P /\ (Q \/ R) <-> (P /\ Q) \/ (P /\ R).
Proof.
  intros P Q R.
  split.
  - intros [HP [HQ | HR]].
    + left. split.
      * apply HP.
      * apply HQ.
    + right. split.
      * apply HP.
      * apply HR.
  - intros [[HP HQ] | [HP HR]].
    + split.
      * apply HP.
      * left. apply HQ.
    + split.
      * apply HP.
      * right. apply HR.     
Qed.

(* Exercise : In map iff *)
Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros A B f l y.
  split.
  - induction l as [| h t IHt].
    + simpl. intro contra. exfalso. apply contra.
    + simpl. intros [HFHY | HINY].
      * exists h. split.
        { apply HFHY. }
        { left. reflexivity. }
      * apply IHt in HINY. destruct HINY as [x' H]. exists x'. split.
        { apply H. }
        { right. apply H. }
  - intro HX. destruct HX as [x' HX'].
    induction l as [| h t IHt].
    + simpl in HX'. destruct HX' as [HFX'Y []].
    + simpl in HX'. simpl. apply and_distributes_over_or in HX'.
      destruct HX' as [HF | HS].
      * left. inversion HF. rewrite H0. apply H.
      * right. apply IHt in HS. apply HS.
Qed.

(* Exercise : In app iff *)
Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l l' a.
  split.
  {
    induction l as [| h t IHt].
    - simpl. intro. right. assumption.
    - simpl. intros [HA | HB].
      + left. left. assumption.
      + apply IHt in HB. destruct HB as [HBA | HBB].
        * left. right. assumption.
        * right. assumption.  
  }
  {
    intros [HL | HL'].
    - induction l as [| h t IHt].
      + simpl in HL. contradiction.
      + simpl in HL. destruct HL as [HLA | HLB].
        * simpl. left. assumption.
        * simpl. right. apply IHt. assumption.
    - induction l as [| h t IHt].
      + simpl. assumption.
      + simpl. right. assumption.
  }
Qed.

(* Exercise : All *)

(* functions returning propositions can be seen as properties of their arguments *)
(* All states that some property P holds of all elements of a list l *)
Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | h::t => P h /\ All P t
  end.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros T P l.
  split.
  {
    induction l as [| h t IHt].
    - simpl. reflexivity.
    - simpl. intro H. split.
      + apply H. left. reflexivity.
      + apply IHt. intros x' H'. apply H. right. apply H'. 
  }
  {
    intros H x.
    induction l as [| h t IHt].
    - simpl. apply ex_falso_quodlibet.
    - simpl. simpl in H. destruct H as [HA HB].
      intros [HX | HIN].
      + rewrite <- HX. assumption.
      + apply IHt. { assumption. } { assumption. } 
  }
Qed.

(* Exercise : combine odd even *)
Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop
  := fun (n:nat) => if oddb n then Podd n else Peven n.

Theorem combine_odd_even_intro :
forall (Podd Peven : nat -> Prop) (n : nat),
  (oddb n = true -> Podd n) ->
  (oddb n = false -> Peven n) ->
  combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even.
  destruct (oddb n).
  - apply H1. reflexivity.
  - apply H2. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  intros Podd Peven n.
  unfold combine_odd_even.
  destruct (oddb n).
  { intros H1 H2. assumption. }
  { intros H1. discriminate. }
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  intros Podd Peven n.
  unfold combine_odd_even.
  destruct (oddb n).
  - intros H1. discriminate.
  - intros H1 H2. assumption.
Qed.

(* Applying Theorems to Arguments *)

(* the statement of a theorem tells us what we can use that theorem for,
just as the type of a computational object tells us
what we can do with that object *)
(* Check plus_comm. *)

(* Operationally, this analogy goes even further:
by applying a theorem, as if it were a function,
to hypotheses with matching types, we can specialize its result
without having to resort to intermediate assertions. *)

Lemma plus_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  (* WORKED IN CLASS *)
  intros x y z.
  rewrite plus_comm.
  rewrite plus_comm.
  (* We are back where we started... *)
Abort.

Lemma plus_comm3_take2 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  assert (H : y + z = z + y).
  { rewrite plus_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

Lemma plus_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite (plus_comm y z).
  reflexivity.
Qed.

Lemma in_not_nil :
  forall A (x : A) (l : list A), In x l -> l != [].
Proof.
  intros A x l H. unfold not. intro Hl. destruct l.
  - simpl in H. destruct H.
  - discriminate Hl.
Qed.

(* Naively, the tactic apply in_not_nil will fail because it cannot infer the value of x *)
Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l != [].
Proof.
  (* WORKED IN CLASS *)
  intros l H.
  Fail apply in_not_nil.
Abort.

(* apply ... with ... *)
Lemma in_not_nil_42_take2 :
  forall l : list nat, In 42 l -> l != [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

(* apply ... in ... *)
Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> l != [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

(* Explicitly apply the lemma to the value for x. *)
Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> l != [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

(* Explicitly apply the lemma to a hypothesis. *)
Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l != [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

(* Search "In_map_iff".
Search "proj1". *)

(* theorem application uses the same inference mechanisms as function application *)

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mult_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

(* Coq vs Set Theory *)

(* a mathematical object can potentially be a member of many different sets;
a term in Coq's logic, on the other hand, is a member of at most one type *)

(* Functional Extensionality : (∀x, f x = g x) → f = g *)

Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. reflexivity. Qed.

(* Functional extensionality is not part of Coq's built-in logic.
This means that some "reasonable" propositions are not provable. *)
Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
   (* Stuck *)
Abort.

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply plus_comm.
Qed.

(* Unfortunately, there is no simple way of telling whether an axiom
is safe to add: hard work by highly-trained trained experts is generally required
to establish the consistency of any particular combination of axioms. *)

(* adding functional extensionality, in particular, is consistent. *)
(* check whether a particular proof relies on any additional axioms,
use the Print Assumptions command *)
(* Print Assumptions function_equality_ex2. *)

(* Exercise : tr_rev_correct *)

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.
Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
  intro X.
  apply functional_extensionality.
  intro l.
  induction l as [| h t IHt].
  - simpl. unfold tr_rev. simpl. reflexivity.
  - simpl. unfold tr_rev in IHt. unfold tr_rev. simpl.
    rewrite <- IHt. 
    assert (H: forall (T : Type) (A B : list T),
      rev_append A B = rev_append A [] ++ B).
    + induction A as [| ha ta IHa].
      * simpl. reflexivity.
      * intro B. simpl.
        rewrite (IHa (ha::B)).
        rewrite (IHa ([ha])).
        rewrite <- app_assoc. simpl.
        reflexivity.
    + apply H.
Qed.

(* Check exists k, double k = 42. *)
(* Propositions and Booleans *)

(*  two different ways of expressing logical claims in Coq:
with booleans (of type bool), and with propositions (of type Prop). *)

Example even_42_bool : evenb 42 = true.
Proof. reflexivity. Qed.

Example even_42_prop : exists k, 42 = double k.
Proof. exists 21. reflexivity. Qed.

Theorem evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

(* Exercise : evenb_double_conv *)

Theorem evenb_double_conv : forall n,
  exists k, 
    n = if evenb n then double k
                else S (double k).
Proof.
  intros. destruct n as [| n'].
  - simpl. exists 0. simpl. reflexivity.
  - 
Admitted.

(* Exercise : even_bool_prop *)

Theorem even_bool_prop : forall n,
  evenb n = true <-> exists k, n = double k.
Proof.
  split.
  - intros. destruct (evenb_double_conv n).
    exists x. rewrite H0.
    destruct (evenb n).
    + reflexivity.
    + discriminate.
  - intros. destruct H.
    rewrite H. apply evenb_double.
Qed.



Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H.
    assert (H': forall x, (x =? x) = true).
    + intro. induction x as [| x' IHx'].
      * simpl. reflexivity.
      * simpl. assumption.
    + apply H'.
Qed.

(* we cannot test whether a general proposition
is true or not in a function definition *)

Fail Definition is_even_prime n :=
  if n = 2 then true
  else false.

(* proof by reflection *)
Example even_1000 : exists k, 1000 = double k.
Proof. exists 500. reflexivity. Qed.

Example even_1000' : evenb 1000 = true.
Proof. reflexivity. Qed.

Search "even_bool_prop".

(* use the boolean formulation to prove the other one without
mentioning the value 500 explicitly: *)
Example even_1000'' : exists k, 1000 = double k.
Proof. apply even_bool_prop. reflexivity. Qed.

Example not_even_1001 : evenb 1001 = false.
Proof.
  (* WORKED IN CLASS *)
  reflexivity.
Qed.

Example not_even_1001' : ~(exists k, 1001 = double k).
Proof.
  (* WORKED IN CLASS *)
  rewrite <- even_bool_prop.
  unfold not.
  simpl.
  intro H.
  discriminate H.
Qed.

Lemma plus_eqb_example : forall n m p : nat,
    n =? m = true -> n + p =? m + p = true.
Proof.
  (* WORKED IN CLASS *)
  intros n m p H.
  rewrite eqb_eq in H.
  rewrite H.
  rewrite eqb_eq.
  reflexivity.
Qed.

(* Exercise : logical connectives *)
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Lemma andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2.
  split.
  - destruct b1, b2.
    + simpl. intros. split.
      * assumption.
      * assumption.
    + simpl. intro. discriminate H.
    + simpl. intro. discriminate H.
    + simpl. intro. discriminate H. 
  - intros [B1 B2].
    rewrite B1, B2. simpl. reflexivity.
Qed.

Lemma orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2.
  split.
  - destruct b1, b2.
    + simpl. intro. left. assumption.
    + simpl. intro. left. assumption.
    + simpl. intro. right. assumption.
    + simpl. intro. discriminate H.
  - intros [B1 | B2].
    + rewrite B1. simpl. reflexivity.
    + rewrite B2. destruct b1.
      * simpl. reflexivity.
      * simpl. reflexivity.
Qed.

(* Exercise : eqb_neq *)
(* Search "contrapositive". *)
Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x != y.
Proof.
Admitted.

(* Exercise : eqb_list *)
Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
                  (l1 l2 : list A) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
Lemma eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
(* FILL IN HERE *) Admitted.

(* Exercise : forallb *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.

Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
 (* FILL IN HERE *) Admitted.

(* Classical vs Constructive Logic *)

(* the following intuitive reasoning principle is not derivable in Coq *)
Definition excluded_middle := forall P : Prop,
  P \/ ~P.
(* universally quantified P in excluded_middle is an arbitrary proposition,
which we know nothing about. We don't have enough information to choose
which of left or right to apply *)
Theorem middle : forall P: Prop,
  P \/ ~P.
Proof.
  intro. left.
Abort.

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. discriminate contra.
Qed.

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n != m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (n =? m)).
  symmetry.
  apply eqb_eq.
Qed.

(* Nonetheless, there is an advantage in not assuming the excluded middle:
statements in Coq can make stronger claims than the analogous statements
in standard mathematics.*)
(*  -> every proof of existence is necessarily constructive.
- constructive logic *)
(* logical system that excluded middle does hold for arbitrary propositions,
are referred to as classical. *)

(* There are many statements that can easily be proven in classical logic
but that have much more complicated constructive proofs,
and there are some that are known to have no constructive proof at all.
Fortunately, like functional extensionality, the excluded middle is
known to be compatible with Coq's logic, allowing us to add it safely as an axiom *)
(* arguments by contradiction, in particular, are infamous for leading to non-constructive proofs *)

(* Exercise : excluded middle irrefutable *)
Theorem excluded_middle_irrefutable: forall (P:Prop),
  ~~(P \/ ~P).
Proof.
  (* FILL IN HERE *) Admitted.

(* Exercise : not exists dist *)
Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~(exists x, ~P x) -> (forall x, P x).
Proof.
  (* FILL IN HERE *) Admitted.

(* Exercise : classical axioms *)
(* Prove that all five propositions (these four plus excluded_middle) are equivalent. *)
Definition peirce := forall P Q: Prop,
  ((P->Q)->P)->P.
Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.
Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P \/ Q.
Definition implies_to_or := forall P Q:Prop,
  (P->Q) -> (~P\/Q).