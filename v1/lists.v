
Module NatList.
Inductive natprod: Type :=
  | pair (n1 n2 : nat).
(* Check (pair 3 5). *)

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Notation "( x , y )" := (pair x y).

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing:
  forall x y : nat,
    (x,y) = (fst (x,y), snd (x,y)).
Proof.
  intros.
  reflexivity.
Qed.

Theorem surjective_pairing' : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

Inductive natlist: Type :=
  | nil
  | cons (h:nat)(t:natlist).

Notation "h :: t" := (cons h t)
  (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2:natlist):natlist :=
  match l1 with
  | nil => l2
  | h1 :: t1 => h1 :: (app t1 l2)
  end.

Notation "x ++ y" := (app x y)
  (right associativity, at level 60).

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.
Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

(* Exercise 2 *)
Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t =>
    match h with
    | 0 => nonzeros t
    | S n => (S n) :: (nonzeros t)
    end
  end.
Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. simpl. reflexivity. Qed.

Fixpoint isodd (n:nat):bool :=
  match n with
  | 0 => false
  | S 0 => true
  | S n => negb (isodd n)
  end.
Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t =>
    match (isodd h) with
    | true => h :: (oddmembers t)
    | false => oddmembers t
    end
  end.
Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. simpl. reflexivity. Qed.

Fixpoint countoddmembers (l:natlist) : nat :=
  match l with
  | nil => 0
  | h :: t =>
    match (isodd h) with
    | true => plus 1 (countoddmembers t)
    | false => countoddmembers t
    end
  end.

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. simpl. reflexivity. Qed.
Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. simpl. reflexivity. Qed.
Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. simpl. reflexivity. Qed.

(* Exersie 3 *)
Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | h1::t1, h2::t2 => [h1;h2] ++ (alternate t1 t2)
  | h1::t1, nil => l1
  | nil, h2::t2 => l2
  | nil, nil => nil
  end.
Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. simpl. reflexivity. Qed.
Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. simpl. reflexivity. Qed.
Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. simpl. reflexivity. Qed.
Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. simpl. reflexivity. Qed.

Definition bag := natlist.

Fixpoint eq_nat (n1 n2 :nat):bool :=
  match n1, n2 with
  | 0, 0 => true
  | 0, _ => false
  | S n1', 0 => false
  | S n1', S n2' => eq_nat n1' n2'
  end.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => 0
  | h :: t => if eq_nat h v then plus 1 (count v t) else (count v t)
  end.
Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. simpl. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. simpl. reflexivity. Qed.

(* Exercise 3 *)

Definition sum : bag -> bag -> bag := app.
Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag := v :: s.
Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool :=
  match (count v s) with
  | 0 => false
  | _ => true
  end.
Example test_member1: member 1 [1;4;1] = true.
Proof. simpl. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. simpl. reflexivity. Qed.

(* Exercise *)

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t => if eq_nat h v then t else h :: (remove_one v t)
  end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t => if eq_nat h v
              then remove_all v t
              else h :: (remove_all v t)
  end.
Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool := 
  match s1 with
  | nil => true
  | h :: t => if member h s2 
              then subset t (remove_one h s2)
              else false
  end.
Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. simpl. reflexivity. Qed.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. simpl. reflexivity. Qed.

(* Reasoning about lists*)
Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity. Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [ | n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.
Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros.
  induction l as [| h t IHt].
  - simpl. reflexivity.
  - simpl. rewrite <- IHt.
Abort.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros.
  induction l1 as [| h1 t1 IHt1].
  - simpl. reflexivity.
  - simpl. rewrite -> IHt1. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Admitted.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros.
  induction l as [| h t IHt].
  - simpl. reflexivity.
  - simpl. rewrite -> app_length, plus_comm. simpl.
    rewrite -> IHt. reflexivity.
Qed.

(* Search rev. *)

(* List Exercise*)
Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros.
  induction l as [| h t IHt].
  - simpl. reflexivity.
  - simpl. rewrite -> IHt. reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros.
  induction l1 as [| h1 t1 IHt1].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IHt1, app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros.
  induction l as [| h t IHt].
  - simpl. reflexivity.
  - simpl. rewrite -> rev_app_distr, IHt. simpl. reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros.
  induction l1 as [| h1 t1 IHt1].
  - simpl. rewrite -> app_assoc. reflexivity.
  - simpl. rewrite -> IHt1. reflexivity.
Qed.

(* Search nonzeros. *)

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros.
  induction l1 as [| h1 t1 IHt1].
  - simpl. reflexivity.
  - simpl.
    {induction h1 as [| n].
      - rewrite -> IHt1. reflexivity.
      - simpl. rewrite -> IHt1. reflexivity. }
Qed.

Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1, l2 with
  | nil, nil => true
  | nil, _ => false
  | h1 :: t1, nil => false
  | h1 :: t1, h2 :: t2 => if eq_nat h1 h2
                          then eqblist t1 t2
                          else false
  end.
Example test_eqblist1 :
  (eqblist nil nil = true).
Proof. simpl. reflexivity. Qed.
Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
Proof. simpl. reflexivity. Qed.
Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof. simpl. reflexivity. Qed.

Theorem eq_nat_refl : forall n:nat, eq_nat n n = true.
Proof.
  intros.
  induction n as [| n'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.


Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
  intros.
  induction l as [| h t IHt].
  - simpl. reflexivity.
  - simpl. rewrite <- IHt. rewrite -> eq_nat_refl. reflexivity.
Qed.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Fixpoint eqb (n m : nat) : bool :=
match n with
| O => match m with
        | O => true
        | S m' => false
        end
| S n' => match m with
          | O => false
          | S m' => eqb n' m'
          end
end.

Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

(* List Exercise, Part2 *)
Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof. intros. simpl. reflexivity. Qed.

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.

Lemma count_leb_succ_helper: forall (b:bool) (n:nat),
  ((if b then S n else n) <=? S (if b then S n else n)) = true.
Proof.
  intros.
  destruct b.
  - simpl. rewrite leb_n_Sn. reflexivity.
  - rewrite leb_n_Sn. reflexivity.
Qed.

Lemma count_leb_succ :
  forall n:nat, forall t:natlist,
    count n t <=? S (count n t) = true.
Proof.
  intros.
  induction t as [| h tail IHtail'].
  - simpl. reflexivity.
  - simpl. rewrite count_leb_succ_helper. reflexivity.
Qed.
  
Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intros.
  induction s as [| h t IHt'].
  - simpl. reflexivity.
  - simpl. destruct h as [| h'].
    + simpl. rewrite count_leb_succ. reflexivity.
    + simpl. rewrite IHt'. reflexivity.
  Qed.

Theorem rev_injective:
  forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2 H.
  rewrite <- rev_involutive. rewrite <- H. rewrite -> rev_involutive.
  reflexivity.
Qed.

(* Option *)
Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n =? O with
               | true => Some a
               | false => nth_error l' (pred n)
               end
  end.

(* Partial Maps*)

End NatList.

Module PartialMap.
Export NatList.

Inductive id : Type :=
| Id (n : nat).

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => eq_nat n1 n2
  end.

Theorem eqb_id_refl : forall x, true = eqb_id x x.
Proof.
  intros.
  destruct x as [n].
  simpl.
  rewrite -> eq_nat_refl.
  reflexivity.
Qed.

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

Definition update (d : partial_map)
  (x : id) (value : nat)
  : partial_map := record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.

(* Exercise *)

Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  intros.
  simpl. rewrite <- eqb_id_refl. reflexivity. Qed.

Theorem update_neq :
forall (d : partial_map) (x y : id) (o: nat),
   eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros.
  simpl. rewrite -> H. reflexivity. Qed.

End PartialMap.