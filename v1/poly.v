Set Warnings "-notation-overridden,-parsing".
From LF Require Export lists.

(* coq_makefile -f _CoqProject *.v -o Makefile *)

(* Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b: bool) (l : boollist). *)

(* Polymorhic Lists *)

(* list is function from Type to Inductive Definition *)
Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Check list.
Check (nil nat).
Check (cons nat 3 (nil nat)).
Check nil.

Fixpoint repeat (X: Type) (x : X) (count : nat) : list X := 
  match count with
  | 0 => nil X
  | S n => cons X x (repeat X x n)
  end.

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.

Module MumbleGrumble.
Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.
Inductive grumble (X:Type) : Type :=
  | d (m : mumble)
  | e (x : X).

(* Which of following are well-typed elements of grumble X for some type X? *)
(* d (b a 5) -> No (need type application)
d mumble (b a 5) -> Yes
d bool (b a 5) -> Yes
e bool true -> Yes
e mumble (b c 0) -> Yes
e bool (b c 0) -> Yes
c -> No (mumble type) *)

(* Check d mumble (b a 5).
Check d bool (b a 5).
Check e bool true.
Check e mumble (b c 0). *)
End MumbleGrumble.

(* Coq was able to use type inference to deduce what types of X,x and count must be
based on how they are used. *)
Fixpoint repeat' X x count : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat' X x count')
  end.

(* When Coq encounters a _, it will attempt to unify all locally available information
-> same mechanism with type inference *)
Definition list123 :=  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).
Definition list123' :=  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(* Arguments directive specifies the name of the function or constructor and then lists its
arguments names, with curly braces around any arguments to be treated as implicit *)
Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

Fixpoint repeat''' {X:Type} (x:X) (count:nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat''' x count')
  end.

(* Use explicit Argument declarations for Inductive constructors.
Marking the parameter of an inductive type as implicit causes it
to become implicit for the type itself, not just for its constructors. *)
Inductive list' {X:Type} : Type :=
  | nil'
  | cons' (x : X) (l : list').

Check list'.

Fixpoint app {X:Type} (l1 l2 : list X) : (list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l : list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X:Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons h t => plus 1 (length t)
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.
Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.
Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.

(* Force implicit arguments to be explicit by prefixing the function name with @ *)
Fail Definition mynil := nil.
Check @nil.
Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y)
                      (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                      (at level 60, right associativity).

Definition list123''' := [1;2;3].

(* Exercise : poly exercies *)
Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  intros.
  induction l as [| h t IHt].
  - simpl. reflexivity.
  - simpl. rewrite IHt. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros.
  induction l as [| h t IHt].
  - simpl. reflexivity.
  - simpl. rewrite IHt. reflexivity.
Qed.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros.
  induction l1 as [| h1 t1 IHt1].
  - simpl. reflexivity.
  - simpl. rewrite -> IHt1. reflexivity.
Qed.

(* Exercise : more poly exercises *)
Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros.
  induction l1 as [| h1 t1 IHt1].
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHt1, app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros.
  induction l as [| h t IHt].
  - simpl. reflexivity.
  - simpl. rewrite rev_app_distr, IHt. simpl. reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

Arguments pair {X} {Y} _ _.

(* Annotation : type_scope tells Coq that this abbreviation should only be used when parsing types
This avoids a clash with multiplication symbol *)
Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X := 
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y := 
  match p with
  | (x, y) => y
  end.

(* Exercise : combine *)

Fixpoint combine {X Y : Type} (l1 : list X) (l2 : list Y): list (X*Y) := 
  match l1, l2 with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x,y) :: combine tx ty
  end.

Compute (combine [1;2] [false;false;true;true]).

(* Exercise split *)

Fixpoint split {X Y : Type} (l : list (X*Y)) : (list X) * (list Y) :=
  match l with
  | nil => (nil, nil)
  | (x,y) :: t => (x :: fst (split t), y :: snd (split t))
  end.
Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. simpl. reflexivity. Qed.

(* Polymorphic Options *)
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
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Module OptionPlayground.

Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.

Arguments Some {X} _.
Arguments None {X}.

Fixpoint nth_error {X:Type} (l:list X) (n:nat) : option X :=
  match l with
  | [] => None
  | h :: t => if n =? 0 then Some h else nth_error t (pred n)
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

(* Exercise : hd_error_poly *)
Definition hd_error {X:Type} (l:list X):option X := 
  match l with 
  | [] => None
  | h :: t => Some h
  end.

Check @hd_error.
Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. reflexivity. Qed.
End OptionPlayground.

(* Functions as Data(Higher Order Function) *)

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

Check @doit3times.
(* Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed. *)
Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

Fixpoint filter {X:Type} (f:X->bool) (l:list X): list X :=
  match l with
  | [] => []
  | h :: t => if f h then h :: filter f t else filter f t
  end.

(* Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity. Qed. *)
Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.
Example test_filter2:
    filter length_is_1
            [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

(* Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).
Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed. *)

(* Anonymous Functions *)

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2':
    filter (fun l => (length l) =? 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

(* Exercise : filter_even_gt7 *)
Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Definition filter_gt7 (l : list nat) : list nat := filter (fun n => 7 <=? n) l.
Example test_filter_gt7_1 :
  filter_gt7 [1;2;6;9;10;3;12;8] = [9;10;12;8].
Proof. simpl. reflexivity. Qed.
Example test_filter_gt7_2 :
  filter_gt7 [5;2;6;19;129] = [19;129].
Proof. simpl. reflexivity. Qed.

(* Exercise : partition *)

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.
Definition oddb (n:nat) : bool := negb (evenb n).

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X
:= match l with
  | [] => ([],[])
  | h :: t => (filter (fun x => test x) l, filter (fun x => negb (test x)) l)
  end.

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

(* Map *)

Fixpoint map {X Y : Type} (f: X->Y) (l : list X): list Y :=
  match l with
  | [] => []
  | h :: t => f h :: map f t
  end.

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Example test_map2:
  map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.

Example test_map3:
    map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

(* Exercise : map_rev *)

Lemma map_distr : forall (X Y : Type) (f : X -> Y)(l1 l2 : list X),
  map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros.
  induction l1 as [| h1 t1 IHt1].
  - simpl. reflexivity.
  - simpl. rewrite IHt1. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros.
  induction l as [| h t IHt].
  - simpl. reflexivity.
  - simpl. rewrite map_distr, IHt. simpl. reflexivity.
Qed.

(* Exercise : flat_map *)

Fixpoint flat_map {X Y:Type} (f: X -> list Y)(l : list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => f h ++ flat_map f t
  end.

Example test_flat_map1:
flat_map (fun n => [n;n;n]) [1;5;4]
= [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

(* Option map *)

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

(* Fold *)

Fixpoint fold {X Y : Type} (f: X -> Y -> Y) (l: list X) (i: Y) : Y :=
  match l with
  | [] => i
  | h :: t => f h (fold f t i)
  end.

Check (fold andb).

Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 :
  fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 :
  fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

(* Functions that construct functions *)
Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.
Definition ftrue := constfun true.
Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.
Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

(* -> expression is actually a right-associative binary operator on types *)
Definition plus3 := plus 3.
Check plus3.
Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

Module Exercises.

(* Exercise : fold_length *)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.
Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

Lemma list_fold_length_inc1: forall X (h: X) (t : list X),
  fold_length (h :: t) = S (fold_length t).
Proof.
  intros.
  induction t as [| a b IHb].
  - simpl. reflexivity.
  - simpl.
Admitted.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros.
  induction l as [| h t IHt].
  - simpl. reflexivity.
  - simpl. rewrite <- IHt. reflexivity.
Admitted.

(* Exercise : fold_map *)

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y
  := fold (fun x a => a ++ [f x]) l [].

Lemma fold_map_distr : forall X Y (f: X->Y) (h:X) (t:list X),
  fold_map f (h :: t) = f h :: fold_map f t.
Proof.
  intros.
  induction t as [| a b IHb].
  - simpl. reflexivity.
  - simpl.
Admitted.

Theorem fold_map_correct :
  forall X Y (f: X->Y) (l : list X),
    fold_map f l = map f l.
Proof.
  intros.
  induction l as [| h t IHt].
  - simpl. reflexivity.
  - simpl. rewrite <- IHt. rewrite fold_map_distr. reflexivity.
Admitted.

(* Exercise : Currying *)
Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).
(* Check prod_curry. *)

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).

Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros.
  (* FILL IN HERE *) Admitted.
Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  (* FILL IN HERE *) Admitted.

(* Church numeral *)
Module Church.
Definition cnat := forall X : Type, (X -> X) -> X -> X.
Definition one : cnat := fun (X : Type) (f : X -> X) (x : X) => f x.
Definition two : cnat := fun (X : Type) (f : X -> X) (x : X) => f (f x).
Definition three : cnat := fun (X : Type) (f : X -> X) (x : X) =>f (f (f x)).
Definition zero : cnat := fun (X : Type) (f : X -> X) (x : X) => x.

(* Exercise : church succ *)

Definition succ (n : cnat) : cnat :=
  fun (X:Type) (f : X -> X) (x : X) => f (n X f x).
Example succ_1 : succ zero = one.
Proof. reflexivity. Qed.
Example succ_2 : succ one = two.
Proof. reflexivity. Qed.
Example succ_3 : succ two = three.
Proof. reflexivity. Qed.

(* Exercise : church plus *)

Definition plus (n m : cnat) : cnat := 
  fun (X:Type) (f: X->X) (x: X) => m X f (n X f x).
Example plus_1 : plus zero one = one.
Proof. reflexivity. Qed.
Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.
Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.

(* Exercise : church mult *)
(* Definition mult (n m : cnat) : cnat :=
  fun (X : Type) (f: X->X) (x: X) =>
    n X (fun(x': X) => (m X f x')) x. *)
Definition mult (n m : cnat) : cnat :=
  fun (X : Type) (f: X->X) (x: X) =>
    n X (m X f) x.
Example mult_1 : mult one one = one.
Proof. reflexivity. Qed.
Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed.
Definition six : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => 
    f (f (f (f (f (f x))))).
Example plus_6 : plus three three = six.
Proof. reflexivity. Qed.
Example mult_3 : mult two three = six.
Proof. reflexivity. Qed.
Example mult_3' : mult two three = plus three three.
Proof. reflexivity. Qed.

(* Exercise : church exp *)
(* Definition cnat' := forall X : Type, (X -> X) -> X -> X. *)
(* Definition exp (n m : cnat) : cnat :=
  m
  cnat
  (mult n)
  one. *)
Definition exp (n m :cnat) : cnat :=
  fun(X:Type) => n (X->X) (m X).

Example exp_2 : exp three zero = one.
Proof. reflexivity. Qed.
Example exp_1 : exp two two = plus two two.
Proof. reflexivity. Qed.
Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof. reflexivity. Qed.

End Church.

End Exercises.