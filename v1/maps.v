(* Import Coq standard library *)
From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.


(* type for the keys that we use to index into our maps *)

(* If you check the result type of string_dec, you'll see that it does not actually
return a bool, but rather a type that looks like {x = y} + {x ≠ y}, called a sumbool,
which can be thought of as an "evidence-carrying boolean."

Formally, an element of sumbool is either a proof that two things are equal or
a proof that they are unequal, together with a tag indicating which *)

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Theorem eqb_string_refl : forall s : string, true = eqb_string s s.
Proof.
  intro. unfold eqb_string. destruct (string_dec s s).
  - reflexivity.
  - destruct n. reflexivity.
Qed.

Theorem eqb_string_true_iff : forall x y : string,
    eqb_string x y = true <-> x = y.
Proof.
  intros.
  unfold eqb_string.
  destruct (string_dec x y) as [| H].
  - subst. split. reflexivity. reflexivity.
  - split.
    + intro contra. discriminate contra.
    + intros H'. rewrite H' in H. destruct H. reflexivity.
Qed.

Theorem eqb_string_false_iff : forall x y : string,
  (eqb_string x y = false) <-> (x <> y).
Proof.
  intros.
  unfold eqb_string.
  destruct (string_dec x y).
  - split.
    + intro contra. discriminate contra.
    + subst. intro H. destruct H. reflexivity.
  - split. intro. assumption. intro. reflexivity.
Qed.

Theorem false_eqb_string : forall x y : string,
   x <> y -> eqb_string x y = false.
Proof.
  intros.
  unfold eqb_string.
  destruct (string_dec x y).
  - rewrite e in H. destruct H. reflexivity.
  - reflexivity.
Qed.

(* Total Maps *)

(* use functions, rather than lists of key-value pairs, to build maps.
The advantage of this representation is that it offers a more extensional
view of maps, where two maps that respond to queries in the same way
will be represented as literally the same thing (the very same function),
rather than just "equivalent" data structures *)

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
  (x : string) (v : A) :=
fun x' => if eqb_string x x' then v else m x'.


Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true)
           "bar" true.

Notation "'_' '!->' v" := (t_empty v) (at level 100, right associativity).
Example example_empty := (_ !-> false).

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Definition examplemap' :=
( "bar" !-> true;
  "foo" !-> true;
  _ !-> false
).

(* Exercise : t_apply_empty *)
Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
    (_ !-> v) x = v.
Proof.
  intros. unfold t_empty. reflexivity.
Qed.

(* Exercise : t_update_eq *)
Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
    (x !-> v ; m) x = v.
Proof.
  intros. unfold t_update. rewrite <- eqb_string_refl. reflexivity.
Qed.

(* Exercise : t_update_neq *)
Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
    x1 <> x2 ->
    (x1 !-> v ; m) x2 = m x2.
Proof.
  intros. unfold t_update. rewrite <- eqb_string_false_iff in H.
  rewrite H. reflexivity.
Qed.

(* Exercise : t_update_shadow *)
Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
    (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros.
  unfold t_update.
  apply functional_extensionality.
  intros.
  destruct (eqb_string x x0). reflexivity. reflexivity.
Qed.

(* Exercise : eqb_stringP *)
Lemma eqb_stringP : forall x y : string,
    reflect (x = y) (eqb_string x y).
Proof.
  intros.
  destruct (eqb_string x y) eqn:E.
  - apply ReflectT. apply eqb_string_true_iff. assumption.
  - apply ReflectF. apply eqb_string_false_iff. assumption.
Qed.

(* Exercise : t_update_same *)
Theorem t_update_same : forall (A : Type) (m : total_map A) x,
    (x !-> m x ; m) = m.
Proof.
  (* intros. unfold t_update. apply functional_extensionality.
  intros. destruct (eqb_string x x0) eqn:E.
  - apply eqb_string_true_iff in E. subst. reflexivity.
  - reflexivity. -> it works *)
  intros. unfold t_update. apply functional_extensionality. intros.
  destruct (eqb_stringP x x0).
  - subst. reflexivity.
  - reflexivity.
Qed.

(* Exercise : t_update_permute *)
Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
    x2 <> x1 ->
    (x1 !-> v1 ; x2 !-> v2 ; m) = (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros.
  unfold t_update. apply functional_extensionality. intro.
  destruct (eqb_stringP x1 x).
  - destruct (eqb_stringP x2 x).
    + destruct H. subst. reflexivity.
    + reflexivity.
  - destruct (eqb_stringP x2 x).
    + reflexivity.
    + reflexivity.
Qed.

(* Partial Map *)

(* use option in total map *)

Definition partial_map (A : Type) := total_map (option A).
Definition empty {A : Type} : partial_map A :=
  t_empty None.
Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

Notation "x '|->' v ';' m" := (update m x v)
(at level 100, v at next level, right associativity).

Notation "x '|->' v" := (update empty x v)
  (at level 100).

Example examplepmap :=
  ("Church" |-> true ; "Turing" |-> false).

(* partial map lemma *)
Lemma apply_empty : forall (A : Type) (x : string),
    @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty. reflexivity.
Qed.

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
    (x |-> v ; m) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq. reflexivity.
Qed.

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
    x2 <> x1 ->
    (x2 |-> v ; m) x1 = m x1.
Proof.
  intros. apply t_update_neq. assumption.
Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
    (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
  intros. apply t_update_shadow.
Qed.

Theorem update_same : forall (A : Type) (m : partial_map A) x v,
    m x = Some v ->
    (x |-> v ; m) = m.
Proof.
  intros. unfold update. rewrite <- H. apply t_update_same.
Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A) x1 x2 v1 v2,
  x2 <> x1 ->
    (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros. unfold update. apply t_update_permute. assumption.
Qed.

