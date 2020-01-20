Set Warnings "-notation-overridden,-parsing".
From LF Require Export logic.
Require Coq.omega.Omega.

(* Inductive Definition of Evenness *)

(* because the nat argument of even appears to the right of the colon, 
it is allowed to take different values in the types of different constructors:
0 in the type of ev_0 and S (S n) in the type of ev_SS. *)

(* In contrast, the definition of list names the X parameter globally,
to the left of the colon, forcing the result of nil and cons to be the same (list X) *)

Inductive even : nat -> Prop :=
| ev_0 : even 0
| ev_SS (n : nat) (H : even n) : even (S (S n)).

(* Inductive list(X:Type) :=
  | nil
  | cons (h:X)(t:list X). *)

Check list.
Check list bool.
Check nil.
Check cons.

Check even.
Check ev_0.
Check ev_SS.
Check (even 0).

(* In an Inductive definition, an argument to the type constructor
on the left of the colon is called a "parameter", whereas an argument
on the right is called an "index".

For example, in Inductive list (X : Type) := ..., X is a parameter;
in Inductive even : nat → Prop := ..., the unnamed nat argument is an index. *)

Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0.
(* | wrong_ev_SS : wrong_ev n -> wrong_ev (S (S n)). *)

(* Inductive even' : nat -> Prop :=
  | ev_0' : even' 0
  | ev_SS' : forall n, even' n -> even' (S (S n)). *)

(* Such "constructor theorems" have the same status as proven theorems. *)

Theorem ev_4 : even 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem ev_4' : even 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

Theorem ev_plus4 : forall n, even n -> even (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

(* Exercise : ev_double *)
Theorem ev_double : forall n,
  even (double n).
Proof.
  intros.
  induction n as [| n' IHn'].
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IHn'.
Qed.

(* Using Evidence in Proof *)

(* analyze the evidence even n directly *)
Theorem ev_inversion :
  forall (n : nat), even n ->
    (n = 0) \/ (exists n', n = S (S n') /\ even n').
Proof.
  intros n E.
  destruct E as [ | m E'].
  - (* E = ev_0 : even 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : even (S (S n')) *)
    right. exists m. split. reflexivity. apply E'.
Qed.

Theorem ev_minus2 : forall n,
  even n -> even (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.
Qed.

(* it doesn't help in the case of evSS_ev since the term
that gets replaced (S (S n)) is not mentioned anywhere *)

Theorem evSS_ev : forall n,
  even (S (S n)) -> even n.
Proof.
  intros n E.
  destruct E as [| n' E'].
Abort.

Theorem evSS_ev : forall n, even (S (S n)) -> even n.
Proof. intros n H. apply ev_inversion in H. destruct H.
 - discriminate H.
 - destruct H as [n' [Hnm Hev]]. injection Hnm.
   intro Heq. rewrite Heq. apply Hev.
Qed.

(* The inversion tactic can detect (1) that the first case (n = 0) does not apply
and (2) that the n' that appears in the ev_SS case must be the same as n.
It has an "as" variant similar to destruct, allowing us to assign names
rather than have Coq choose them. *)

Theorem evSS_ev' : forall n,
  even (S (S n)) -> even n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  (* We are in the E = ev_SS n' E' case now. *)
  apply E'.
Qed.

Theorem one_not_even : ~even 1.
Proof.
  intros H. apply ev_inversion in H.
  destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Check not.
Check False.
Check True.

Theorem one_not_even' : ~even 1.
  intros H. inversion H. Qed.

(* Exercise : Inversion Practice *)

Theorem SSSSev__even : forall n,
  even (S (S (S (S n)))) -> even n.
Proof.
  intros.
  inversion H.
  inversion H1.
  apply H3.
Qed.

(* Exercise : even5 nonsense *)

(* inversion False?? *)

Theorem even5_nonsense :
  even 5 -> 2 + 2 = 9.
Proof.
  intro.
  simpl.
  inversion H.
  inversion H1.
  inversion H3.
Qed.

Theorem principle_of_explosion: forall P:Prop, False -> P.
Proof.
  intros.
  inversion H.
Qed.

(* The inversion tactic does quite a bit of work. When applied to equalities,
as a special case, it does the work of both discriminate and injection. In addition,
it carries out the intros and rewrites that are typically necessary
in the case of injection. *)

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  inversion H.
  reflexivity.
  (* injection H.
  intros.
  rewrite H0, H1. *)
Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra.
  discriminate contra.
  (* inversion contra. *)
Qed.

Lemma ev_even_firsttry : forall n,
  even n -> exists k, n = double k.
Proof.
  intros n H.
  inversion H as [| n' H'].
  - exists 0. reflexivity.
  (* By performing case analysis on E, we were able to reduce the original result
  to a similar one that involves a different piece of evidence for even: namely E'
  ∃k', n' = double k',*)
  - assert (I: (exists k', n' = double k') -> 
      (exists k, S (S n') = double k) ).
    {
      intros.
      destruct H1 as [k' HK'].
      exists (S k').
      simpl. rewrite HK'. reflexivity.
    }
    apply I.
    (* Need induction hypothesis *)
Abort.

(* Induction on Evidence *)

Lemma ev_even : forall n,
  even n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E'
       with IH : exists k', n' = double k' *)
    destruct IH as [k' Hk'].
    rewrite Hk'. exists (S k'). reflexivity.
Qed.

Theorem ev_even_iff : forall n,
  even n <-> exists k, n = double k.
Proof.
  intros n. split.
  - (* -> *) apply ev_even.
  - (* <- *) intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

(* Exercise : ev_sum *)

Theorem ev_sum : forall n m, even n -> even m -> even (n + m).
Proof.
  intros.
  induction H as [| n' IHn' IHn''].
  - simpl. assumption.
  - simpl. apply ev_SS. apply IHn''.
Qed.

(* Exercise : even'_ev *)
Inductive even' : nat -> Prop :=
| even'_0 : even' 0
| even'_2 : even' 2
| even'_sum n m (Hn : even' n) (Hm : even' m) : even' (n + m).

Theorem even'_ev : forall n, even' n <-> even n.
Proof.
  intro.
  split.
  - intro. induction H as [| | n' m' IHn' IHn IHm' IHm].
    + apply ev_0.
    + apply (ev_SS 0 ev_0).
    + assert(H: forall n m :nat, even n -> even m -> even (n+m)).
      {
        intros.
        induction H as [| nn' IHnn'].
        - simpl. apply H0.
        - simpl. apply ev_SS. apply IHIHnn'.
      }
      apply H.
      * apply IHn.
      * apply IHm.
  - intro. induction H as [| n' IHn' IHn''].
    + apply even'_0.
    + assert(H: forall n: nat, S (S n) = n + 2). 
      {
        intro. induction n as [| m IHm].
        - simpl. reflexivity.
        - simpl. rewrite IHm. reflexivity.
      }
      rewrite H. apply even'_sum.
      * apply IHn''.
      * apply even'_2. 
Qed.

(* Exercise : ev_ev__ev *)

Theorem ev_ev__ev_fail : forall n m,
  even (n+m) -> even n -> even m.
Proof.
  intros n m H1 H2.
  apply even'_ev.
  apply even'_ev in H1.
  apply even'_ev in H2.
  assert (Hzero: forall a b : nat, 0 = a + b -> a = 0 /\ b = 0).
  {
    intro. induction a as [| a' IHa'].
    - simpl. intros. split. reflexivity. symmetry. assumption.
    - simpl. intros. discriminate H.
  }
  inversion H1.
  - apply Hzero in H0. destruct H0 as [HN0 HM0].
    rewrite HM0.
    apply even'_0.
  - assert (H: forall a b : nat, 2 = a + b ->
    (a = 0 /\ b = 2) \/ (a = 1 /\ b = 1) \/ (a = 2 /\ b = 0)).
    {
      intros.
      destruct a as [| a'].
      - destruct b as [| b'].
        + simpl in H. discriminate H.
        + simpl in H. rewrite <- H. left. split. reflexivity. reflexivity.
      - destruct b as [| b'].
        + simpl in H.
          assert (HH: forall k:nat, k + 0  = k).
          {
            intro. induction k as [| k' IHk'].
            - simpl. reflexivity.
            - simpl. rewrite IHk'. reflexivity. 
          }
          rewrite HH in H. rewrite <- H.
          right. right. split. reflexivity. reflexivity.
        + assert (HH: forall k l, 2 = (S k) + (S l) -> k = 0 /\ l = 0).
        {
          intro. induction k as [| k' IHk'].
          - simpl. intros. destruct l as [| l'].
            + split. reflexivity. reflexivity.
            + discriminate H3.
          - intros. simpl in H3. inversion H3. apply Hzero in H5.
            destruct H5 as [HK' HSL]. discriminate HSL.
        }
          apply HH in H. destruct H. rewrite H, H3. right. left.
          split. reflexivity. reflexivity. 
    }
    apply H in H0. destruct H0 as [HNM | [HNM' | HNM'']].
    + destruct HNM. rewrite H3. apply even'_2.
    + destruct HNM'. rewrite H0 in H2. apply even'_ev in H2. inversion H2.
    + destruct HNM''. rewrite H3. apply even'_0.
  - (* Stuck ... *)
Abort.

Theorem ev_ev__ev : forall n m,
  even (n+m) -> even n -> even m.
Proof.
  intros. induction H0.
  - simpl in H. assumption.
  - simpl in H. apply evSS_ev in H. apply IHeven in H. assumption.
Qed.

Theorem ev_ev__ev' : forall n m,
  even (n+m) -> even n -> even m.
Proof.
  intros.
  apply even'_ev.
  apply even'_ev in H.
  apply even'_ev in H0.
  (* ?? *)
Abort.

(* Exercise : ev_plus_plus *)

Lemma even_explode : forall n m x,
  even (n+m) -> even ((n+x) + (m+x)).
Admitted.

Theorem ev_plus_plus : forall n m p,
  even (n+m) -> even (n+p) -> even (m+p).
Proof.
  intros n m p H0 H1.
  apply even_explode with (x:=p) in H0.
  apply (ev_ev__ev (n+p) (m+p)) in H0.
  assumption. assumption.
Qed.

Module Playground.
(* Two argument proposition can be tought of relation *)
Inductive le : nat -> nat -> Prop :=
  | le_n n : le n n
  | le_S n m (H : le n m) : le n (S m).
Notation "m <= n" := (le m n).

Theorem test_le1 :
  3 <= 3.
Proof.
  apply le_n. Qed.
Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n. Qed.
Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2. Qed.

End Playground.
Definition lt (n m:nat) := le (S n) m.
Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
  | sq n : square_of n (n * n).
Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).
Inductive next_even : nat -> nat -> Prop :=
  | ne_1 n : even (S n) -> next_even n (S n)
  | ne_2 n (H : even (S (S n))) : next_even n (S (S n)).

(* Exercise : le exercises *)
Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros.
  rewrite <- H0.
  assumption.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros.
  induction n as [| n' IHn'].
  - apply le_n.
  - apply le_S. apply IHn'.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m' IHm'].
  - intros. inversion H. apply le_n.
  - intros. inversion H.
    + apply le_n.
    + apply le_S. apply IHm' in H1. assumption.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros.
  inversion H.
  - apply le_n.
  - assert (Haux : forall a : nat, a <= S a).
    {
      intro. apply le_S. apply le_n.
    }
    apply (le_trans n (S n) m).
    + apply Haux.
    + apply H1.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros.
  induction a as [| a' IHa'].
  - simpl. apply O_le_n.
  - simpl. apply n_le_m__Sn_le_Sm. apply IHa'.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  unfold lt.
  intros n1 n2 m H.
  split.
  - assert (Haux: forall a b, S(a+b) = S a + b).
  { intros. simpl. reflexivity. }
    assert (Haux': S n1 <= S n1 + n2).
  { apply le_plus_l. }
    rewrite Haux in H.
    apply le_trans with (m:=(S n1)) (n:=(S n1 + n2)) (o:=m).
    + assumption.
    + assumption.
  - assert (Haux: forall a b, S(a+b) = S b + a).
  { intros. simpl. rewrite plus_comm. reflexivity. }
    assert (Haux': S n2 <= S n2 + n1).
  { apply le_plus_l. }
    rewrite Haux in H.
    apply le_trans with (m:=(S n2)) (n:=(S n2 + n1)) (o:=m).
    + assumption.
    + assumption.
Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt.
  intros.
  apply n_le_m__Sn_le_Sm.
  assert (Haux : n <= S n).
  { intros. apply le_S. apply le_n. }
  apply le_trans with (m:=n)(n:=(S n))(o:=m).
  - assumption.
  - assumption.
Qed.

Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
  intros. generalize dependent n.
  induction m.
  - intros. destruct n.
    + apply le_n.
    + simpl in H. discriminate H.
  - intros. destruct n.
    + apply O_le_n.
    + simpl in H. apply IHm in H. apply n_le_m__Sn_le_Sm.
      assumption.
Qed.

Theorem leb_correct : forall n m,
  n <= m ->
  n <=? m = true.
Proof.
  intros. generalize dependent n.
  induction m.
  - intros. inversion H. simpl. reflexivity.
  - intros. destruct n.
    + simpl. reflexivity.
    + simpl. apply IHm. apply Sn_le_Sm__n_le_m in H. assumption.
Qed.

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  intros.
  apply leb_complete in H.
  apply leb_complete in H0.
  apply leb_correct.
  apply le_trans with (m:=n)(n:=m)(o:=o).
  - assumption.
  - assumption.
Qed.

Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  split.
  - apply leb_complete.
  - apply leb_correct.
Qed.

Module R.
(* Exercise : R_provability *)
Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 m n o (H : R m n o) : R (S m) n (S o)
   | c3 m n o (H : R m n o) : R m (S n) (S o)
   | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
   | c5 m n o (H : R m n o) : R n m o.

(* Which of the following propositions are provable?
   R 1 1 2
   R 2 2 6 -> Not provable *)
Theorem R_1_1_2 : R 1 1 2.
Proof.
  apply c2. apply c3. apply c1.
Qed.

(* If we dropped constructor c5 from the definition of R, would the set of
provable propositions change? Briefly (1 sentence) explain your answer. 
No. changing sequence of applying c2, c3 is sufficient.
*)

(* If we dropped constructor c4 from the definition of R, would the set of
provable propositions change? Briefly (1 sentence) explain your answer.
No. it is equivalent to excluding c2, c3.
*)

(* Exwercise : R_fact *)
Definition fR : nat -> nat -> nat := plus.
Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Admitted.
End R.

(* Exercise : subsequence *)

Inductive subseq : list nat -> list nat -> Prop :=
  | subseq_nil(l: list nat) : subseq [] l
  | subseq_head(h: nat) (l1 l2 : list nat)(H: subseq l1 l2) : subseq (h::l1) (h::l2)
  | subseq_extra(x:nat) (l1 l2 : list nat)(H: subseq l1 l2) : subseq l1 (x::l2).

Theorem subseq_refl : forall l : list nat, subseq l l.
Proof.
  intros.
  induction l.
  - apply subseq_nil.
  - apply subseq_head. apply IHl.
Qed.


Theorem subseq_app : forall l1 l2 l3 : list nat,
  subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
  intros.
  induction H.
  - apply subseq_nil.
  - simpl. apply subseq_head. apply IHsubseq.
  - simpl. apply subseq_extra. apply IHsubseq.
Qed.

Theorem subseq_app' : forall l1 l2 l3 : list nat,
  subseq l1 l2 -> subseq l1 (l3 ++ l2).
Proof.
  intros.
  generalize dependent l1.
  generalize dependent l2.
  induction l3.
  - simpl. intros. assumption.
  - simpl. intros. apply subseq_extra. apply IHl3 in H. apply H.
Qed.

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
  intros.
  generalize dependent l1.
  induction H0.
  - intros. inversion H. apply subseq_nil.
  - intros. inversion H.
    + apply subseq_nil.
    + apply subseq_head. apply IHsubseq. apply H3.
    + apply IHsubseq in H3. apply subseq_extra. assumption.
  - intros.
    assert(Haux: forall (n:nat)(l:list nat),
      n :: l = [n] ++ l).
    {
      intros.
      destruct l.
      - simpl. reflexivity.
      - simpl. reflexivity.
    }
    rewrite Haux. apply subseq_app'. apply IHsubseq. assumption.
Qed.

(* Exercise : R provability 2 *)

Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.

(* Which of the following propositions are provable?
R 2 [1;0]
R 1 [1;2;1;0]
R 6 [3;2;1;0] : Not provable *)
Theorem R_2_1_0: R 2 [1;0].
Proof.
  apply c2. apply c2. apply c1.
Qed.

Theorem R_1_1_2_1_0: R 1 [1;2;1;0].
Proof.
  apply c3. apply c2.
  apply c3. apply c3. apply c2.
  apply c2. apply c2.
  apply c1.
Qed.

(* Case Study : Regular Expression *)

(*
- The expression EmptySet does not match any string.
- The expression EmptyStr matches the empty string [].
- The expression Char x matches the one-character string [x].
- If re1 matches s1, and re2 matches s2, then App re1 re2 matches s1 ++ s2.
- If at least one of re1 and re2 matches s, then Union re1 re2 matches s.
- Finally, if we can write some string s as the concatenation of a sequence of
strings s = s_1 ++ ... ++ s_k, and the expression re matches each one of
the strings s_i, then Star re matches s. *)

Inductive reg_exp {T : Type} : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp)
  | Union (r1 r2 : reg_exp)
  | Star (r : reg_exp).

Inductive exp_match {T} : list T -> reg_exp -> Prop :=
| MEmpty : exp_match [] EmptyStr
| MChar x : exp_match [x] (Char x)
| MApp s1 re1 s2 re2
      (H1 : exp_match s1 re1)
      (H2 : exp_match s2 re2) :
      exp_match (s1 ++ s2) (App re1 re2)
| MUnionL s1 re1 re2
          (H1 : exp_match s1 re1) :
          exp_match s1 (Union re1 re2)
| MUnionR re1 s2 re2
          (H2 : exp_match s2 re2) :
          exp_match s2 (Union re1 re2)
| MStar0 re : exp_match [] (Star re)
| MStarApp s1 s2 re
          (H1 : exp_match s1 re)
          (H2 : exp_match s2 (Star re)) :
          exp_match (s1 ++ s2) (Star re).
        
Notation "s =~ re" := (exp_match s re) (at level 80).

Example reg_exp_ex1 : [1] =~ Char 1.
Proof. apply MChar. Qed.
Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2] _).
  - apply MChar.
  - apply MChar.
Qed.
Example reg_exp_ex3 : ~([1; 2] =~ Char 1).
Proof.
  intros H.
  inversion H.
Qed.

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.
Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl.
  (* apply (MApp [1] _ [2;3] _).
  - apply MChar.
  - apply (MApp [2] _ [3] _).
    + apply MChar.
    + apply (MApp [3] _ [] _).
      * apply MChar.
      * apply MEmpty. *)
  apply (MApp [1]).
  {apply MChar. }
  apply (MApp [2]).
  {apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

(* every string s that matches re also matches Star re. *)
Lemma MStar1 :
  forall T s (re : @reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s []).
  - assumption.
  - apply MStar0.
Qed.

(* Exercise : exp_match_ex1 *)

Lemma empty_is_empty : forall T (s : list T),
  ~(s =~ EmptySet).
Proof.
  intros. intro H.
  inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : @reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros. destruct H as [Hsre1 | Hsre2].
  - apply MUnionL. assumption.
  - apply MUnionR. assumption.
Qed.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros.
  induction ss as [| s ss' IHss'].
  - simpl. apply MStar0.
  - simpl. apply MStarApp.
    + apply H. simpl. left. reflexivity.
    + apply IHss'. intros.
      apply H. simpl. right. assumption.
Qed.

(* Exercise : reg_exp_of_list_spec *)

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  intros.
  symmetry.
  split.
  {
    intros.
    rewrite H.
    assert (Haux: forall T (s:list T), s =~ reg_exp_of_list s).
    {
      intros.
      induction s.
      - simpl. apply MEmpty.
      - simpl. apply (MApp [x]).
        + apply MChar.
        + apply IHs.
    }
    apply Haux.
  }
  {
    intros.
    generalize dependent s2.
    induction s1.
    - intros. destruct s2.
      + reflexivity.
      + simpl in H. inversion H. inversion H3. rewrite <- H5 in H1. discriminate H1.
    - intros. destruct s2.
      + simpl in H. inversion H.
      + simpl in H. inversion H. inversion H3. rewrite <- H5 in H1. simpl in H1.
        inversion H1. rewrite H9 in H4. apply IHs1 in H4.
        rewrite H4. reflexivity.
  }
Qed.

(* If a regular expression re matches some string s,
then all elements of s must occur as character literals somewhere in re. *)

Fixpoint re_chars {T} (re : reg_exp) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Theorem in_re_match : forall T (s : list T) (re : reg_exp) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* WORKED IN CLASS *)
  - (* MEmpty *)
    apply Hin.
  - (* MChar *)
    apply Hin.
  - simpl. rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.
  - (* MStarApp *)
    simpl. rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.

(* Exercise : re_not_empty *)

(* whether a regular expression matches some string *)

Fixpoint re_not_empty {T : Type} (re : @reg_exp T) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char x => true
  | App re1 re2 => re_not_empty re1 && (re_not_empty re2)
  | Union re1 re2 => re_not_empty re1 || re_not_empty re2
  | Star re => true
  end.
Lemma re_not_empty_correct : forall T (re : @reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros.
  split.
  {
    intros.
    destruct H as [s H].
    induction H
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
    - reflexivity.
    - reflexivity.
    - simpl. rewrite IH1. rewrite IH2. simpl. reflexivity.
    - simpl. rewrite IH. simpl. reflexivity.
    - simpl. rewrite IH. apply orb_true_iff.
      right. reflexivity.
    - reflexivity.
    - reflexivity. 
  }
  {
    intros.
    induction re.
    - discriminate H.
    - exists []. apply MEmpty.
    - exists [t]. apply MChar.
    - simpl in H. apply andb_true_iff in H.
      destruct H.
      apply IHre1 in H. destruct H.
      apply IHre2 in H0. destruct H0.
      exists (x ++ x0).
      apply (MApp x _ x0 _). assumption. assumption.
    - simpl in H. apply orb_true_iff in H. destruct H.
      + apply IHre1 in H. destruct H.
        exists x. apply MUnionL. assumption.
      + apply IHre2 in H. destruct H.
        exists x. apply MUnionR. assumption.
    - exists []. apply MStar0. 
  }
Qed.

(* remember tactic *)

Lemma star_app: forall T (s1 s2 : list T) (re : @reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  (* lost a very important bit of information from H1:
  the fact that s1 matched something of the form Star re *)
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
Abort.

(* induction over a Prop hypothesis only works properly
with hypotheses that are completely general *)

Lemma star_app: forall T (s1 s2 : list T) (re re' : reg_exp),
  re' = Star re ->
  s1 =~ re' ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Abort.

(* The tactic remember e as x causes Coq to
(1) replace all occurrences of the expression e by the variable x, and
(2) add an equation x = e to the context. *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *) discriminate.
  - (* MChar *) discriminate.
  - (* MApp *) discriminate.
  - (* MUnionL *) discriminate.
  - (* MUnionR *) discriminate.
  - (* MStar0 *)
    injection Heqre'. intros Heqre'' s H. apply H.
  - (* MStarApp *)
    injection Heqre'. intros H0.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * rewrite H0. reflexivity.
      * apply H1.
Qed.

(* Exercise : exp_match_ex2 *)
Lemma MStar'' : forall T (s : list T) (re : reg_exp),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros T s re H.
  remember (Star re) as re'.
  induction H
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
  |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
  |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - injection Heqre'. intro. exists [].
    simpl. split. reflexivity.
    intros. destruct H0.
  - exists [s1;s2']. split. simpl. rewrite app_nil_r. reflexivity.
Admitted.

(* Exercise : pumping *)

(* Pumping Lemma :
any sufficiently long string s matching a regular expression re can be "pumped"
by repeating some middle section of s an arbitrary number of times
to produce a new string also matching re. *)

Module Pumping.

(* the minimum length for strings s to guarantee "pumpability." *)
Fixpoint pumping_constant {T} (re : @reg_exp T) : nat :=
  match re with
  | EmptySet => 0
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star _ => 1
  end.

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

(* if s =~ re and if the length of s is at least the pumping constant of re,
then s can be split into three substrings s1 ++ s2 ++ s3 in such a way that
s2 can be repeated any number of times and the result, when combined with s1 and s3
will still match re.

Since s2 is also guaranteed not to be the empty string,
this gives us a (constructive!) way to generate strings matching re
that are as long as we like. *)

(* the omega tactic, which is enabled by the following Require,
is helpful in several places for automatically completing tedious low-level arguments
involving equalities or inequalities over natural numbers *)
Import Coq.omega.Omega.

(* | MEmpty : exp_match [] EmptyStr
| MChar x : exp_match [x] (Char x)
| MApp s1 re1 s2 re2
      (H1 : exp_match s1 re1)
      (H2 : exp_match s2 re2) :
      exp_match (s1 ++ s2) (App re1 re2)
| MUnionL s1 re1 re2
          (H1 : exp_match s1 re1) :
          exp_match s1 (Union re1 re2)
| MUnionR re1 s2 re2
          (H2 : exp_match s2 re2) :
          exp_match s2 (Union re1 re2)
| MStar0 re : exp_match [] (Star re)
| MStarApp s1 s2 re
          (H1 : exp_match s1 re)
          (H2 : exp_match s2 (Star re)) :
          exp_match (s1 ++ s2) (Star re). *)

Lemma pumping : forall T (re : @reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 != [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. omega.
  (* MChar *)
  - simpl. omega.
   (* MApp  *)
  - 
Admitted.

End Pumping.

(* Case Study : Improving Reflection *)

Theorem filter_not_empty_In : forall n l,
  filter (fun x => n =? x) l != [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l =  *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (n =? m) eqn:H.
    + (* n =? m = true *)
      intros _. rewrite eqb_eq in H. rewrite H.
      left. reflexivity.
    + (* n =? m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(* defining an inductive proposition that yields a better case-analysis principle
for n =? m. *)
(*  Intuitively, it states that the property P is reflected in (i.e., equivalent to)
the boolean b: that is, P holds if and only if b = true *)

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT (H : P) : reflect P true
| ReflectF (H : ~P) : reflect P false.

(* P ↔ b = true and reflect P b are indeed equivalent *)

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  (* WORKED IN CLASS *)
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.

(* Exercise : reflect_iff *)
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H. destruct b.
  - inversion H. split.
    + intro. reflexivity.
    + intro. assumption.
  - inversion H. split.
    + intro. apply H0 in H1. destruct H1.
    + intro. discriminate.
Qed.

(* The advantage of reflect over the normal "if and only if" connective is that,
by destructing a hypothesis or lemma of the form reflect P b, we can perform
case analysis on b while at the same time generating appropriate hypothesis
in the two branches (P in the first subgoal and ¬ P in the second). *)

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

(* smoother proof of filter_not_empty_In' *)

Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l != [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l =  *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (eqbP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(* Exercise : eqbP_practice *)
Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.
Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros n l.
  induction l as [| h t IHt].
  - simpl. intro. intros H0. destruct H0.
  - simpl. destruct (eqbP n h) as [H | H].
    + simpl. intros. discriminate H0.
    + simpl. intros. apply IHt in H0. intro H'.
      destruct H'.
      * destruct H. symmetry. assumption.
      * destruct H0. assumption.
Qed.

(* Additional Exercises *)

(* Exercise : noshutter_defn *)

(* We say that a list "stutters" if it repeats the same element consecutively *)
Definition hd {X:Type} (default : X)(l:list X) : X :=
  match l with
  | nil => default
  | h :: t => h
  end.

Inductive nostutter {X:Type} : list X -> Prop :=
| nost_nil : nostutter []
| nost_one (x : X) : nostutter [x]
| nost_app (x : X)( l : list X)
            (H1: nostutter l)
            (H2: reflect (x=(hd x l)) false) : nostutter (x::l).

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof.
  apply nost_app.
  { apply nost_app.
    { apply nost_app.
      { apply nost_app.
        { apply nost_app.
          { apply nost_one. }
          simpl. apply ReflectF. intro. discriminate.
          }
          simpl. apply ReflectF. intro. discriminate.
          }
          simpl. apply ReflectF. intro. discriminate.
          }
          simpl. apply ReflectF. intro. discriminate.
          }
          simpl. apply ReflectF. intro. discriminate.
Qed.

Example test_nostutter_2: nostutter (@nil nat).
Proof. apply nost_nil. Qed.

Example test_nostutter_3: nostutter [5].
Proof. apply nost_one. Qed.

Example test_nostutter_4: not (nostutter [3;1;1;4]).
Proof.
  simpl. intro.
  inversion H.
  inversion H0.
  simpl in H7. inversion H7.
  destruct H8. reflexivity.
Qed.

(* Exercise : filter_challenge *)
Inductive InOrderMerge {X:Type} : list X -> list X -> list X -> Prop :=
| iom_self (l : list X) : InOrderMerge l l []
| iom_comm (l1 l2 l3 : list X)
            (H : InOrderMerge l1 l2 l3) : InOrderMerge l1 l3 l2
| iom_appL (x : X) (l1 l2 l3 : list X)
            (H : InOrderMerge l1 l2 l3) : InOrderMerge (x::l1) (x::l2) l3
| iom_appR (x : X) (l1 l2 l3 : list X)
            (H : InOrderMerge l1 l2 l3) : InOrderMerge (x::l1) l2 (x::l3).

Theorem filter_spec : forall T (l1 : list T) (test : T -> bool),
  exists l2 l3, InOrderMerge l1 l2 l3 /\ (filter test l1) = l2 /\ (filter (fun x => negb (test x)) l1) = l3.
Proof.
  intros.
  induction l1 as [| h t IHt].
  - exists []. exists []. simpl. split.
    + apply iom_self.
    + split. reflexivity. reflexivity.
  - destruct IHt. destruct H. destruct H. destruct H0.
    destruct (test h) eqn:E.
    + exists (h :: x). exists x0. split.
      { apply iom_appL. assumption. }
      { split. 
        - simpl. rewrite E. rewrite H0. reflexivity.
        - simpl. rewrite E. simpl. apply H1. }
    + exists x. exists (h :: x0). split.
      { apply iom_appR. assumption. }
      { split.
        - simpl. rewrite E. assumption.
        - simpl. rewrite E. simpl. rewrite H1. reflexivity. }
Qed.

(* Exercise : filter_challenge_2 *)

(* Exercise : palindromes *)
Inductive pal {X:Type} : list X -> Prop :=
| pal_nil : pal []
| pal_one (x : X) : pal [x]
| pal_app (x : X) (l : list X) (H: pal l) : pal (x :: (l ++ [x])).

(* A palindrome is a sequence that reads the same backwards as forwards. *)
Theorem pal_app_rev: forall T l, @pal T (l ++ rev l).
Proof.
  intros. induction l.
  - simpl. apply pal_nil.
  - simpl. rewrite app_assoc.
    apply (pal_app x (l ++ rev l)). 
    assumption.
Qed.

Theorem pal_rev: forall T l, pal l -> l = @rev T l.
Proof.
  intros. induction H.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite rev_app_distr. simpl. rewrite <- IHpal. reflexivity.
Qed.

(* Exercise : palindrome_converse *)
Theorem pal_rev_conv: forall T l, l = (@rev T l) -> pal l.
Proof.
  intros T l.
  induction l as [| h t IHt].
  - simpl. intro. apply pal_nil.
  - simpl. intro.
Admitted.

(* Exercise : NoDup *)
(* Fixpoint In (A : Type) (x : A) (l : list A) : Prop :=
   match l with
   |  => False
   | x' :: l' => x' = x \/ In A x l'
   end *)

Inductive disjoint {X:Type}: list X -> list X -> Prop :=
| disj_nil (l : list X) : disjoint l []
| disj_comm (l1 l2 : list X) (H : disjoint l1 l2) : disjoint l2 l1
| disj_appL (x : X) (l1 l2 : list X)
            (H1 : disjoint l1 l2)
            (H2 : reflect (~(In x l2)) true) : disjoint (x::l1) l2
| disj_appR (x : X) (l1 l2 : list X)
            (H1 : disjoint l1 l2)
            (H2 : reflect (~(In x l1)) true) : disjoint l1 (x::l2).

Inductive NoDup {X:Type} : list X -> Prop :=
| nodup_nil : NoDup []
| nodup_app (x : X) (l : list X)
            (H1 : NoDup l)
            (H2 : reflect (~(In x l)) true) : NoDup (x::l).

(* Exercise : pigeonhole_principle *)
Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros. induction l.
  - destruct H.
  - simpl in H. destruct H as [H1 | H2].
    + rewrite H1. exists []. exists l. simpl. reflexivity.
    + apply IHl in H2. destruct H2. destruct H.
      rewrite H. exists (x0 :: x1). exists x2. simpl. reflexivity.
Qed.

(* repeats : at least two elements in list have same value *)
Inductive repeats {X:Type} : list X -> Prop :=
| re_intro (x : X) (l : list X)
          (H: reflect (In x l) true) : repeats (x::l)
| re_app (x : X)(l : list X)(H : repeats l) : repeats (x::l).

(* list l2 represents a list of pigeonhole labels,
and list l1 represents the labels assigned to a list of items *)
Theorem pigeonhole_principle: forall (X:Type) (l1 l2:list X),
   excluded_middle ->
   (forall x, In x l1 -> In x l2) ->
   length l2 < length l1 ->
   repeats l1.
Proof.
  intros X l1. induction l1 as [|x l1' IHl1'].
  - intros. simpl in H1. destruct l2.
    + simpl in H1. unfold lt in H1. inversion H1.
    + simpl in H1. unfold lt in H1. inversion H1.
  - intros.  
Admitted.

