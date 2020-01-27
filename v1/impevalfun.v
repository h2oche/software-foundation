From Coq Require Import omega.Omega.
From Coq Require Import Arith.Arith.
From LF Require Import imp maps.

(* A Broken Evaluator *)
Open Scope imp_scope.
Fixpoint ceval_step1 (st : state) (c : com) : state :=
  match c with
    | SKIP =>
        st
    | l ::= a1 =>
        (l !-> aeval st a1 ; st)
    | c1 ;; c2 =>
        let st' := ceval_step1 st c1 in
        ceval_step1 st' c2
    | TEST b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_step1 st c1
          else ceval_step1 st c2
    (* bogus *)
    | WHILE b1 DO c1 END =>
        st 
    (* Cannot guess decreasing argument of fix *)
    (* | WHILE b1 DO c1 END =>
    if (beval st b1) then
      ceval_step1 st (c1;; WHILE b1 DO c1 END)
    else st *)
    
  end.
Close Scope imp_scope.

(* A Step-Indexed Evaluator *)

(* pass an additional parameter to the evaluation function that tells it how long to run *)
Open Scope imp_scope.
Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
  match i with
  | O => empty_st
  | S i' =>
    match c with
      | SKIP =>
          st
      | l ::= a1 =>
          (l !-> aeval st a1 ; st)
      | c1 ;; c2 =>
          let st' := ceval_step2 st c1 i' in
          ceval_step2 st' c2 i'
      | TEST b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step2 st c1 i'
            else ceval_step2 st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then let st' := ceval_step2 st c1 i' in
               ceval_step2 st' c i'
          else st
    end
  end.
Close Scope imp_scope.

(* One thing that is not so nice about this evaluator is that we can't tell,
from its result, whether it stopped because the program terminated normally or
because it ran out of gas *)

(* distinguish between normal and abnormal termination by "option" *)
Open Scope imp_scope.
Fixpoint ceval_step3 (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | SKIP =>
          Some st
      | l ::= a1 =>
          Some (l !-> aeval st a1 ; st)
      | c1 ;; c2 =>
          match (ceval_step3 st c1 i') with
          | Some st' => ceval_step3 st' c2 i'
          | None => None
          end
      | TEST b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step3 st c1 i'
            else ceval_step3 st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then match (ceval_step3 st c1 i') with
               | Some st' => ceval_step3 st' c i'
               | None => None
               end
          else Some st
    end
  end.
Close Scope imp_scope.

(* auxiliary notation to hide the plumbing involved in repeatedly matching
against optional states *)
Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).
Open Scope imp_scope.
Fixpoint ceval_step (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | SKIP =>
          Some st
      | l ::= a1 =>
          Some (l !-> aeval st a1 ; st)
      | c1 ;; c2 =>
          LETOPT st' <== ceval_step st c1 i' IN
          ceval_step st' c2 i'
      | TEST b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then LETOPT st' <== ceval_step st c1 i' IN
               ceval_step st' c i'
          else Some st
    end
  end.
Close Scope imp_scope.

Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None => None
  | Some st => Some (st X, st Y, st Z)
  end.

(* Exercise : pup_to_n *)
Definition pup_to_n : com := (
  Y ::= 0 ;;
  WHILE ~ (0 = X) DO
    Y ::= Y + X ;;
    X ::= X - 1
  END
)%imp.

Example pup_to_n_1 :
  test_ceval (X !-> 5) pup_to_n
  = Some (0, 15, 0).
Proof. reflexivity. Qed.

(* Exercise : peven *)
(* sets Z to 0 if X is even and sets Z to 1 otherwise *)
Definition peven : com := (
  WHILE (~ (0 = X)) && (~ (1 = X)) DO
    X ::= X - 2
  END
  ;;
  TEST X = 1
  THEN Z ::= 1
  ELSE Z ::= 0
  FI
).

Example peven_test1 :
  test_ceval (X !-> 10) peven
  = Some (0, 0, 0).
Proof. reflexivity. Qed.

Example peven_test2 :
  test_ceval (X !-> 9) peven
  = Some (1, 0, 1).
Proof. reflexivity. Qed.

(* Relational vs. Step-Indexed Evaluation *)
Theorem ceval_step__ceval: forall c st st',
      (exists i, ceval_step st c i = Some st') ->
      st =[ c ]=> st'.
Proof.
  intros c st st' H.
  inversion H as [i E].
  clear H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [| i' IHi'].
  - intros c st st' H. simpl in H. discriminate H.
  - intros c st st' H.
    destruct c;
      simpl in H; inversion H; subst; clear H; try (constructor; reflexivity).
    (* E_Seq *)
    + destruct (ceval_step st c1 i') eqn:Hc1.
      * apply E_Seq with s.
      { apply IHi' in Hc1. assumption. }
      { apply IHi' in H1. assumption. }
      * discriminate H1.
    (* E_If *)
    + destruct (beval st b) eqn:Hb.
      * apply E_IfTrue.
      { assumption. }
      { apply IHi' in H1. assumption. }
      * apply E_IfFalse.
      { assumption. }
      { apply IHi' in H1. assumption. }
    (* E_While *)
    + destruct (beval st b) eqn:Hb;
      destruct (ceval_step st c i') eqn:Hc; try discriminate H1.
      * apply E_WhileTrue with s.
      { assumption. }
      { apply IHi' in Hc. assumption. }
      { apply IHi' in H1. assumption. }
      * inversion H1. subst. apply E_WhileFalse. assumption.
      * inversion H1. subst. apply E_WhileFalse. assumption.
Qed.

Theorem ceval_step_more: forall i1 i2 st st' c,
  i1 <= i2 ->
  ceval_step st c i1 = Some st' ->
  ceval_step st c i2 = Some st'.
Proof.
induction i1 as [|i1']; intros i2 st st' c Hle Hceval.
  - (* i1 = 0 *)
    simpl in Hceval. discriminate Hceval.
  - (* i1 = S i1' *)
    destruct i2 as [|i2']. inversion Hle.
    assert (Hle': i1' <= i2') by omega.
    destruct c.
    + (* SKIP *)
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + (* ::= *)
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + (* ;; *)
      simpl in Hceval. simpl.
      destruct (ceval_step st c1 i1') eqn:Heqst1'o.
      * (* st1'o = Some *)
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      * (* st1'o = None *)
        discriminate Hceval.
    + (* TEST *)
      simpl in Hceval. simpl.
      destruct (beval st b); apply (IHi1' i2') in Hceval;
        assumption.
    + (* WHILE *)
      simpl in Hceval. simpl.
      destruct (beval st b); try assumption.
      destruct (ceval_step st c i1') eqn: Heqst1'o.
      * (* st1'o = Some *)
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite -> Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      * (* i1'o = None *)
        simpl in Hceval. discriminate Hceval. Qed.

(* Exercise : ceval__ceval_step *)
Theorem le_n_S : forall n m,
  (n <= m) -> (S n <= S m).
Proof.
  intros n m H.
  induction H.
  - apply le_n.
  - apply le_S. apply IHle.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros.
  induction n as [| n' IHn'].
  - apply le_n.
  - apply le_S. apply IHn'.
Qed.

Lemma leb_conv : forall i1 i2, (i1 <=? i2) = false -> i2 < i1.
Proof.
  unfold lt.
  induction i1.
  - simpl. intros i2 contra. discriminate contra.
  - intros i2 H. destruct i2.
    + apply le_n_S. apply O_le_n.
    + apply le_n_S. apply IHi1. simpl in H. assumption.
Qed.

Theorem ceval__ceval_step: forall c st st',
      st =[ c ]=> st' ->
      exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st' Hce.
  induction Hce; try (exists 1; simpl; subst; reflexivity).
  - destruct IHHce1 as [i1 E1]; destruct IHHce2 as [i2 E2].
    exists (S (i1+i2)).
    apply ceval_step_more with (i2:=i1+i2) in E1.
    apply ceval_step_more with (i2:=i1+i2) in E2.
    simpl. destruct (ceval_step st c1 (i1+i2)) eqn:E.
    + inversion E1. subst. assumption.
    + inversion E1.
    + omega.
    + omega.
  - destruct IHHce as [i' E].
    exists (S i').
    simpl. rewrite H. assumption.
  - destruct IHHce as [i' E].
    exists (S i').
    simpl. rewrite H. assumption.
  - exists 1. simpl. rewrite H. reflexivity.
  - destruct IHHce1 as [i1 E1]; destruct IHHce2 as [i2 E2].
    exists (S (i1+i2)).
    apply ceval_step_more with (i2:=i1+i2) in E1.
    apply ceval_step_more with (i2:=i1+i2) in E2.
    simpl. destruct (beval st b) eqn:E.
    + destruct (ceval_step st c (i1 + i2)) eqn:E'.
      * inversion E1. subst. assumption.
      * inversion E1.
    + discriminate H.
    + omega.
    + omega.
Qed.

Theorem ceval_and_ceval_step_coincide: forall c st st',
  st =[ c ]=> st'
<-> exists i, ceval_step st c i = Some st'.
Proof.
intros c st st'.
split. apply ceval__ceval_step. apply ceval_step__ceval.
Qed.

(* Determinism of Evaluation Again *)
Theorem ceval_deterministic' : forall c st st1 st2,
     st =[ c ]=> st1 ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 H1 H2.
  apply ceval_and_ceval_step_coincide in H1.
  apply ceval_and_ceval_step_coincide in H2.
  inversion H1 as [i1 E1].
  inversion H2 as [i2 E2].
  apply ceval_step_more with (i2:=i1+i2) in E1.
  apply ceval_step_more with (i2:=i1+i2) in E2.
  rewrite E1 in E2. inversion E2. reflexivity.
  omega. omega.
Qed.