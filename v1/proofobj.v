Set Warnings "-notation-overridden,-parsing".
From LF Require Export indprop.

(* Curry-Howard Correspondence *)

(* Provability in Coq is represented by concrete evidence.
When we construct the proof of a basic proposition, we are actually building
a tree of evidence, which can be thought of as a data structure. *)

(* programming and proving is same thing :
proofs are simply programs that manipulate evidence*)

(* Evidence <-> Data
Proposition <-> Type

A:B
A has type B
A is proof of B
A is evidence for B*)

Print even.
(* ev_SS is a constructor that takes two arguments —
a number n and evidence for the proposition even n —
and yields evidence for the proposition even (S (S n)) *)
Check ev_SS.

Theorem ev_4 : even 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

(* As with ordinary data values and functions, we can use the Print command
to see the proof object that results from this proof script. *)
Print ev_4.

Check (ev_SS 2 (ev_SS 0 ev_0)).
(* ===> even 4 *)

(* we can think of ev_SS as a primitive "evidence constructor" that,
when applied to a particular number, wants to be further applied to evidence
that that number is even; its type, *)

(* Proof Scripts *)

(* When Coq is following a proof script, what is happening internally is that
it is gradually constructing a proof object — a term whose type is the proposition
being proved. The tactics between Proof and Qed tell it how to build up
a term of the required type *)

(* At any given moment, Coq has constructed a term with a "hole"
(indicated by ?Goal here, and so on), and it knows what type of evidence is needed
to fill this hole. *)

Theorem ev_4'' : even 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.

(* Each hole corresponds to a subgoal, and the proof is finished when
there are no more subgoals. At this point, the evidence we've built stored
in the global context under the name given in the Theorem command.

Tactic proofs are useful and convenient, but they are not essential:
in principle, we can always construct the required evidence by hand, as shown above.
Then we can use Definition (rather than Theorem) to give a global name directly
to this evidence. *)

Definition ev_4''' : even 4 := ev_SS 2 (ev_SS 0 ev_0).

Print ev_4.
(* ===> ev_4    =   ev_SS 2 (ev_SS 0 ev_0) : even 4 *)
Print ev_4'.
(* ===> ev_4'   =   ev_SS 2 (ev_SS 0 ev_0) : even 4 *)
Print ev_4''.
(* ===> ev_4''  =   ev_SS 2 (ev_SS 0 ev_0) : even 4 *)
Print ev_4'''.
(* ===> ev_4''' =   ev_SS 2 (ev_SS 0 ev_0) : even 4 *)

(* Exercise : eight_is_even *)
Theorem ev_8 : even 8.
Proof.
  Show Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Definition ev_8' : even 8 := ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0))).

(* Quantifiers, Implications, Functions *)

(* In Coq's computational universe (where data structures and programs live),
there are two sorts of values with arrows in their types:
constructors introduced by Inductively defined data types, and functions.

Similarly, in Coq's logical universe (where we carry out proofs),
there are two ways of giving evidence for an implication:
constructors introduced by Inductively defined propositions, and... functions! *)

Theorem ev_plus4 : forall n, even n -> even (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

(* We're looking for an expression whose type is ∀ n, even n → even (4 + n) —
that is, a function that takes two arguments (one number and a piece of evidence)
and returns a piece of evidence! *)

Definition ev_plus4' : forall n, even n -> even (4 + n) :=
  fun (n : nat) => fun (H : even n) =>
    ev_SS (S (S n)) (ev_SS n H).

(* The second argument's type, even n, mentions the value of the first argument, n. *)
Definition ev_plus4'' (n : nat) (H : even n) : even (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).
Check ev_plus4''.

(* both implication (→) and quantification (∀) correspond to functions on evidence.
In fact, they are really the same thing: → is just a shorthand for
a degenerate use of ∀ where there is no dependency,

i.e., no need to give a name to the type on the left-hand side of the arrow:
∀(x:nat), nat  = ∀(_:nat), nat = nat → nat *)

Definition ev_plus2 : Prop :=
  forall n, forall (E : even n), even (n + 2).

Definition ev_plus2' : Prop :=
  forall n, forall (_ : even n), even (n + 2).

(* In general, "P → Q" is just syntactic sugar for "∀ (_:P), Q". *)
Definition ev_plus2'' : Prop :=
  forall n, even n -> even (n + 2).

(* Programming with tactics *)

(* build programs using tactics rather than explicit terms *)

Definition add1 : nat -> nat.
intro n.
Show Proof.
apply S.
Show Proof.
apply n. Defined.

Print add1.
Compute add1 2.

(* Logical Connectives as Inductive Types *)

Module Props.

(* P ∧ Q as consisting of a pair of two proofs: one for P and another one for Q *)

Module And.
Inductive and (P Q : Prop) : Prop :=
| conj : P -> Q -> and P Q.
End And.

(* the only difference is that prod takes Type arguments,
whereas and takes Prop arguments. *)

(* This similarity should clarify why "destruct" and "intros" patterns
can be used on a conjunctive hypothesis *)
Print prod.

(* Similarly, the "split" tactic actually works for any inductively defined
proposition with exactly one constructor *)
Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
Qed.

(* We can also use it to build proofs directly, using pattern-matching *)
Definition and_comm'_aux P Q (H : P /\ Q) : Q /\ P :=
  match H with
  | conj HP HQ => conj HQ HP
  end.
Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

Check and_comm'.

(* Exercise : conj_fact *)
Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun(P : Prop) => fun (Q : Prop) => fun (R : Prop) =>
    fun (H1 : P /\ Q) =>
      fun (H2 : Q /\ R) => 
        match H1 with
        | conj EP EQ =>
          match H2 with
          | conj EQ' ER' => conj EP ER'
          end
        end.

Definition conj_fact' : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  (* forall P Q R : Prop, *)
  fun (P Q R : Prop) (H1 : P /\ Q) (H2 : Q /\ R) =>
    match H1 with
    | conj EP EQ =>
      match H2 with
      | conj EQ' ER' => conj EP ER'
      end
    end.

Definition conj_fact'' : forall P Q R, P /\ Q -> Q /\ R -> P /\ R.
intros.
Show Proof.
destruct H.
Show Proof.
destruct H0.
Show Proof.
split.
Show Proof.
apply H.
Show Proof.
apply H2.
Show Proof.
Defined.

(* Disjuction *)
Module Or.
Inductive or (P Q : Prop) : Prop :=
| or_introl : P -> or P Q
| or_intror : Q -> or P Q.
End Or.

(* Exercise : or_commut'' *)
Definition or_comm : forall P Q, P \/ Q -> Q \/ P :=
  fun (P Q : Prop) (H : P \/ Q) =>
    match H with
    | or_introl EP => or_intror EP
    | or_intror EQ => or_introl EQ
    end.

Definition or_comm' : forall P Q, P \/ Q -> Q \/ P.
intros.
Show Proof.
destruct H.
Show Proof.
right.
Show Proof.
apply H.
Show Proof.
left.
Show Proof.
apply H.
Show Proof.
Defined.

(* Existential Quantification *)

(* The ex_intro constructor then offers a way of constructing evidence for ex P,
given a witness x and a proof of P x. *)

Module Ex.
Inductive ex {A : Type} (P : A -> Prop) : Prop :=
| ex_intro : forall x : A, P x -> ex P.
(* | ex_intro (x:A)(H: P x) : ex P *)
End Ex.

Check ex (fun n => even n).

Definition some_nat_is_even : exists n, even n :=
  ex_intro even 4 (ev_SS 2 (ev_SS 0 ev_0)).

(* Exercise : ex_ev_Sn *)
(* Intuition : odd number exists *)
Definition ex_ev_Sn : ex (fun n => even (S n)).
Show Proof.
exists 1.
Show Proof.
apply ev_SS.
Show Proof.
apply ev_0.
Show Proof.
Defined.

Definition ex_ev_Sn' : ex (fun n => even (S n)) :=
  ex_intro (fun n => even (S n)) 1 (ev_SS 0 ev_0).


(* True and False *)

(* It has one constructor (so every proof of True is the same,
so being given a proof of True is not informative.) *)

Inductive True : Prop :=
  | I : True.

(* False is an inductive type with no constructors
— i.e., no way to build evidence for it. *)
Inductive False : Prop := .
End Props.

(* Eqaulity *)

Module MyEquality.
Inductive eq {X:Type} : X -> X -> Prop :=
| eq_refl : forall x, eq x x.

Notation "x == y" := (eq x y)
                    (at level 70, no associativity)
                    : type_scope.

(* Coq treats as "the same" any two terms that are convertible according to
a simple set of computation rules. *)

Lemma four: 2 + 2 == 1 + 3.
Proof.
  apply eq_refl.
Qed.

(* The "reflexivity" tactic that we have used to prove equalities up to now
is essentially just shorthand for apply eq_refl. *)

Definition four' : 2 + 2 == 1 + 3 :=
  eq_refl 4.
Definition singleton : forall (X:Type) (x:X), []++[x] == x::[] :=
  fun (X:Type) (x:X) => eq_refl [x].

(* Exercise : equality__leibniz_equality *)

(* The inductive definition of equality implies Leibniz equality:
what we mean when we say "x and y are equal" is that every property on P
that is true of x is also true of y. *)

Lemma equality__leibniz_equality : forall (X : Type) (x y: X),
  x == y -> forall P:X->Prop, P x -> P y.
Proof.
  intros X x y H. inversion H. intros. apply H2.
Qed.

(* Exercise : leibniz_equality__equality *)

(* in fact, the inductive definition of equality is equivalent to Leibniz equality: *)

Lemma leibniz_equality__equality : forall (X : Type) (x y: X),
  (forall P:X->Prop, P x -> P y) -> x == y.
Proof.
  Show Proof.
  intros.
  Show Proof.
  apply (H (fun z => x == z)).
  Show Proof.
  apply eq_refl.
  Show Proof.
Qed.
End MyEquality.

(* Inversion, Again *)

(* 
How Inversion Behaves :

1) takes a hypothesis H whose type P is inductively defined, and  
2) for each constructor C in P's definition,
  2-1) generates a new subgoal in which we assume H was built with C,
  2-2) adds the arguments (premises) of C to the context of the subgoal as 
  extra hypotheses,
  2-3) matches the conclusion (result type) of C against the current goal
  and calculates a set of equalities that must hold in order for C to be applicable,
  2-4) adds these equalities to the context (and, for convenience, rewrites them
  in the goal), and
  2-5) if the equalities are not satisfiable (e.g., they involve things like S n = O),
  immediately solves the subgoal. *)

(* Example: If we invert a hypothesis built with eq,
there is again only one constructor, so only one subgoal gets generated.
Now, though, the form of the eq_refl constructor does give us some extra information:
it tells us that the two arguments to eq must be the same!
The inversion tactic adds this fact to the context. *)