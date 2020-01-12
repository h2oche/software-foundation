(* Inductive Day: Type :=
  | Monday
  | Tuesday
  | Wednesday
  | Thursday
  | Friday
  | Saturday
  | Sunday.

Definition NextDay(d:Day) : Day := 
  match d with
  | Monday => Tuesday
  | Tuesday => Wednesday
  | Wednesday => Thursday
  | Thursday => Friday
  | Friday => Saturday
  | Saturday => Sunday
  | Sunday => Monday
  end.

(* Compute (NextDay Monday).
Compute (NextDay (NextDay Monday)). *)

Example testNextDay:
  (NextDay (NextDay Saturday)) = Monday. *)

(* Proof. simpl. reflexivity. Qed. *)

Module NatPlayground.
Inductive Bool : Type :=
  | True
  | False.

Definition negb(b: Bool) : Bool :=
  match b with
  | True => False
  | False => True
  end.

Definition andb (b1: Bool) (b2: Bool) :=
  match b1 with
  | True => b2
  | False => False
  end.

Definition orb(b1: Bool) (b2: Bool) :=
  match b1 with
  | True => True
  | False => b2
  end.

Example testOrb1: (orb False False) = False.
Proof. simpl. reflexivity. Qed.
Example testOrb2: (orb False False) = False.
Proof. simpl. reflexivity. Qed.
Example testOrb3: (orb False False) = False.
Proof. simpl. reflexivity. Qed.
Example testOrb4: (orb False False) = False.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Definition nandb(b1: Bool)(b2:Bool) : Bool := 
  match b1 with
  | True =>
    match b2 with
    | True => False
    | False => True
    end
  | False => match b2 with
    | True => True
    | False => False
    end
  end.

Example testNanb1: (nandb True False) = True.
Proof. simpl. reflexivity. Qed.
Example testNanb2: (nandb True True) = False.
Proof. simpl. reflexivity. Qed.
Example testNanb3: (nandb False False) = False.
Proof. simpl. reflexivity. Qed.
Example testNanb4: (nandb False True) = True.
Proof. simpl. reflexivity. Qed.

Definition and3(b1: Bool)(b2: Bool)(b3: Bool):Bool := (b1 && b2) && b3.

Example testAnd3: (and3 True True True) = True.
Proof. simpl. reflexivity. Qed.

Check True.
Check and3.

Inductive Rgb : Type :=
  | Red
  | Green
  | Blue.

Inductive Color : Type :=
  | Black
  | White
  | Primary(p: Rgb).

Definition Monochrome(c : Color) :=
  match c with
  | Black => True
  | White => True
  | Primary q => False
  end.

Definition IsRed(c : Color) := 
  match c with
  | Black => True
  | White => True
  | Primary q => False
  end.

Inductive Bit : Type :=
  | B_0
  | B_1.

Inductive Nat: Type :=
  | O
  | S (n : Nat).

Definition Pred (n : Nat):Nat :=
  match n with 
  | O => O
  | S n' => n'
  end.

Example predTest1: (Pred O) = O.
Proof. simpl. reflexivity. Qed.
Example predTest2: (Pred (S (S O))) = (S O).
Proof. simpl. reflexivity. Qed.

Fixpoint Evenb (n : Nat): Bool :=
  match n with
  | O => True
  | S O => False
  | S (S n') => Evenb n'
  end.

Example evenTest1: (Evenb (S (S (S O)))) = False.
Proof. simpl. reflexivity. Qed.

Fixpoint Add(n1: Nat)(n2:Nat):Nat := 
  match n1 with
  | O => n2
  | S n' => S (Add n' n2)
  end.

Fixpoint Mult(n1 n2 : Nat): Nat :=
  match n1 with
  | O => O
  | S n' => Add n2 (Mult n' n2)
  end. 

Fixpoint Sub(n1 n2 : Nat):Nat :=
  match n2 with
  | O => n1
  | S n' => Sub (Pred n1) n'
  end.

Fixpoint Fac(n:Nat):Nat :=
  match n with
  | O => S O
  | S n' => Mult n (Fac n')
  end.

Fixpoint EqNat(n1 n2 : Nat):Bool :=
  match n1, n2 with
  | O, O => True
  | O, _ => False
  | S n1', O => False
  | S n1', S n2' => EqNat n1' n2'
  end.
  
Theorem Plus_O_N: forall n: Nat, (Add O n) = n.
Proof.
  intros n.
  reflexivity.
  (* simpl. *)
Qed.

Theorem Plus_Id: forall n m : Nat, m = n -> Add n n = Add m m .
Proof.
  intros n m.
  intros H.
  (* rewrite <- H. *)
  rewrite -> H.
  reflexivity.
Qed.

Theorem Plud_Id2: forall n m o : Nat, n = m -> m = o -> Add n m = Add m o.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite -> H1.
  rewrite <- H2.
  (* rewrite -> H1. *)
  reflexivity.
Qed.

Theorem  PlusOneNeqZero: forall n : Nat, EqNat (Add n (S O)) O = False.
Proof.
  intros n.
  destruct n as [ | n'] eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

End NatPlayground.

Fixpoint Fac(n:nat):nat :=
  match n with
  | O => S O
  | S n' => mult n (Fac n')
  end.

Example testFac1: Fac 3 = 6.
Proof. simpl. reflexivity. Qed.

Check (S (S O)).
Check S.

Compute (plus 3 2).
Compute (mult 3 2).

Theorem IdentityFnTwice:
  forall f:bool -> bool,
    (forall x:bool, f x = x) -> (forall b:bool, f (f b) = b).
Proof.
  intros.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem andbEQorb:
  forall b c : bool,
    (andb b c = orb b c) -> b = c.
Proof.
  intros b c.
  destruct b as [] eqn:E1.
  - destruct c as [] eqn: E2.
    + intros. reflexivity.
    + simpl. intros H. rewrite -> H. reflexivity.
  - destruct c as [] eqn: E2.
    + discriminate.
    + intros. reflexivity.
Qed.

Inductive bin: Type :=
  | Z
  | A (n: bin)
  | B (n: bin).

Fixpoint incr (m:bin):bin :=
  match m with
  | Z => A Z
  | A m' => B m'
  | B m' => A (incr m')
  end.

Fixpoint bit2nat (m:bin):nat :=
  match m with
  | Z => 0
  | A m' => plus (S O) (bit2nat m')
  | B m' => plus (S (S O)) (bit2nat m')
  end.

Example bit2natTest: bit2nat (A Z) = 1.
Proof. simpl. reflexivity. Qed.

