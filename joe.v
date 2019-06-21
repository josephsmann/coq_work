Check 3.

Require Import Arith.
Require Import ZArith.
Require Import Bool.

Print Scope Z_scope.

Locate "_ + _".

Check (3 + 2)%Z.

Open Scope Z_scope.

Locate "_ + _".

Check 3 + 2.

Check fun (f g: nat->nat)(n:nat) => f ( g n).

Check fun x: nat => (x + x)%nat.

Check (fun n (z:Z) f => (n+(Z.abs_nat (f z)))%nat).

Check fun n p : nat =>
  (let diff := n-p in
   let square := diff*diff in
       square * (square +n))%nat.

Goal forall X Y: Prop, X->Y->X.
  exact 
(fun XX : Prop => 
fun YY:Prop => fun a:XX => fun _:YY => a).
Qed.

Goal forall X Y Z: Prop, (X->Y)->(Y->Z)->(X->Z).
Proof.
intros x y z A B.
exact 
(fun xx => B (A xx)).
Qed.

Goal forall X Y Z: Prop, (X->Y)->(Y->Z)->(X->Z).
Proof.
exact 
  (fun X : Prop =>
   fun Y : Prop =>
   fun Z : Prop =>
   fun XY : (X->Y) =>
   fun YZ : (Y->Z) => 
   fun A : X => YZ (XY A)).
Qed.

Goal forall X Y Z: Prop, (X->Y)->(Y->Z)->(X->Z).
Proof. 
  intros.
  Show Proof. 
  apply H0, H, H1.

(*   apply H0. 
  apply H.
  apply H1.
 *)
Qed. 

Goal forall X Y Z : Prop, (X->Y->Z) -> (X->Y) -> (X->Z).
Proof.
  exact
  ( fun X Y Z: Prop => fun (XYZ : X->Y->Z) (XY : X->Y) (A :X) =>
    XYZ A (XY A) ).
  Show Proof.
Qed.

Goal forall X Y Z : Prop, (X->Y->Z) -> (X->Y) -> (X->Z).
Proof.
  intros.
  apply H.
  apply H1.
  Show Proof.
  apply H0.
  apply H1.

  Show Proof.
Qed.

Goal forall X Y Z: Prop, (X \/ Y /\ Z) -> (X \/ Y)  /\ (X \/ Z).
Proof.
  intros x y z a.
  destruct a as [xx | [yy zz]].
    + split.
      * left. exact xx.
      * left. exact xx.
    + split.
      * right. exact yy.
      * right. exact zz.
Qed.
  
Goal forall X Y Z: Prop, (X \/ Y /\ Z) -> (X \/ Y)  /\ (X \/ Z).
Proof.
  intros x y z [xx | [yy zz]].
  split.
  left. exact xx.
  left. exact xx.
  split.
  right. exact yy.
  right. exact zz.
  Show Proof.
Qed.

Goal forall X Y Z: Prop, (X \/ Y /\ Z) -> (X \/ Y)  /\ (X \/ Z).
Proof.
  intros x y z [xx | [yy zz]].
  - split.
    + left. exact xx.
    + left. exact xx.
  - split.
    + right. exact yy.
    + right. exact zz.
Qed.

(**** ~ takes a prop and returns a __constant function__  A => False *****)

Goal forall X: Prop, ~ ~ ~ X -> ~ X.
Proof.
  intros x A.
  intros B. (* this takes the goal "~ x" and makes "x" a premiss and False a goal ...*)
  apply A. (* goal was False, so  ~ ~ ~ A -> False  which implies that ~ ~ A must be true if ~ ~ ~ A -> False was true. *)
  intros C. (* this takes the goal "~ ~ x" and makes "~ x" a premiss and False a goal ...*)
  apply C.
  exact B.
Qed.

Print not.
(*
not = fun A : Prop => A -> False
     : Prop -> Prop
*) 
Print False.
Print intros.

Goal forall X: Prop, ~ ~ ~ X -> ~ X.
Proof.
  intros x A.
(*   Show Proof. *)
  intros B. (* this takes the goal "~ x" (because "~ x" is "x => False") and makes "x" a premiss and False a goal ...*)
(*   Show Proof. *)
  apply A. (* goal was False, so  ~ ~ ~ A -> False  == which implies that ~ ~ A must be true if ~ ~ ~ A -> False was true. *)
  Show Proof.
  intros C. (* this takes the goal "~ ~ x" and makes "~ x" a premiss called C and False a goal ...*)
  Show Proof.
  exact (C B).
  Show Proof.
Qed.

(* Goal forall X: Prop, X -> ~ ~ X.
Proof.
  intros x A.
   *)

Goal forall X: Prop, ~ ~ ~ X -> ~ X.
Proof.
  intros x A.
  intros B. (* this takes the goal "~ x" (because "~ x" is "x => False") and makes "x" a premiss and False a goal ...*)
  apply A. (* goal was False, so  ~ ~ ~ A -> False  == which implies that ~ ~ A must be true if ~ ~ ~ A -> False was true. *)
  exact (fun C => C B). 
(* think first C goes into assumptions and C B goes into conclusions. ~ ~ x ==  (~ x -> False). 
so C binds with ~ x (== x -> False) and B C == (x -> False) C
which == False which goes below. 

~ ~ x
~ x -> False (def)
~ x | False    (intros)
(~ x) x (exact) False   (exact (fun C => C B)  -- C binds with (~ x) and then C B evaluates to False
Qed.
*)
Qed.

(* intros correspond to a lambda abstraction *)
(* ~ A  is a proof of False given A *)


Goal forall X: Prop, ~ ~ ~ X -> ~ X.
Proof.
  intros xP A x.
  exact (A (fun C => C x)).
  Show Proof.
(*
 (fun (xP : Prop) (A : ~ ~ ~ xP) (x : xP) =>
 A (fun C : ~ xP => C x))
remember (fun C: ~ xP => C x) == ~ ~ xP so
and A == (~ ~ x => False) so
A (...) = False

give me 
~~X  => False 
I'll give you
X => False
*)
Qed.


Goal forall (X : Type)  (x y: X), (forall p : X->Prop, (p x = p y) )-> (x = y).
Proof.
  intros X x y A.
  exact	 (A (fun z => x = z)) 
  


Open Scope nat_scope.
Theorem plus_O_n : (forall n : nat, 0 + n = n).
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.


Theorem j : (forall a : Prop, a -> a).
  intro prop_a. (* translate proposition into statement? *)
  intro imp. (* introducte statement *)
  exact imp.
Qed.

Theorem trans_imp : ( forall A B C : Prop, (A -> B) /\ (B -> C) -> (A -> C)).
(* 
if I had A then I would have C is the conclusion. 
let me demonstrate that I can derive this.
If I have A, then from AB I would have B
now, with B and BC I should have C.
in summary, if I have A, I would have C. Qed.

also. if my theorem returns an implication (A->C) it actually returns
a function f: A->C

*)
Proof.
  
  intros.
  destruct H as [ABB BC].
  apply BC.
  apply ABB.
  apply H0.
Qed.

Print trans_imp.


Theorem or_imp : (forall A B C:Prop, ((A \/ B) -> C) -> ((A->C) \/ (B->C))).
Proof.
  intros.
  left.
  intros.
  apply H.
  left.
  apply H0.
Qed.

(* prove ((A v B)->C)  -> ((A -> C) v (B -> C)) *)
Theorem and_imp : (forall A B C:Prop, ((A \/ B) -> C) -> ((A->C) /\ (B->C))).
Proof.
  intros. (* enter A B C and AvB->C *)
  split.  (* break goal into 2 goals A->C and B->C *)
  intros Ha. (* break A->C into hyp A and goal C *)
  apply H. (* apply AvB->C to C to get AvB as goal *)
  left.    (* choose left side of AvB because we've got Ha *)
  apply Ha. (* Appyl Ha to the goal A  *)
  intros Hb. (* do the same thing that we did to A to B *)
  apply H.
  right.
  apply Hb.
Qed.

Print and_imp.

(*(A \u21d2 (B \u21d2 C)) \u21d2 ((A \u2227 B) \u21d2 C)*)
Theorem ii_ai : (forall A B C: Prop, (A->(B->C))->((A/\B)->C)).
Proof.
  intros.
  apply H.
  destruct H0 as [pA pB].
  apply pA.
  destruct H0 as [pA pB].
  apply pB.
Qed.

Print ii_ai.

Lemma example3 : forall A B, A \/ B -> B \/ A.
Proof.
  intros.
  destruct H as [H1 | H2].
  right.
  apply H1.  (* could have used assumption *)
  left.      (* chooses left hand target of dysjunction *)
 assumption. (* assumption finds the premiss needed and applies it *)
Qed.  
  

Lemma e4 : 3 <= 5.
  apply le_S. (* applying implication returns stronger assertion .. *)
  apply le_S.
  apply le_n.
Qed.

Check le_S.
(*(A \u21d2 (B \u21d2 C)) \u21d2 ((A \u2227 B) \u21d2 C)*)
Theorem ii_ai2 : (forall A B C: Prop, (A->(B->C))->((A/\B)->C)).
Proof.
  intros.
  apply H.
  

Qed.

Variables A B C: Prop.

Check A.
Check trans_imp.


Proof.
  intro a.
  intro b.
  intro c.
  intro con.  
  destruct con as [AB BC]. 
  (* admit *)
  (* Because I have a->c, I assume or 'intro a' and try to prove 'c' *)
  intro HA.
  (* then I 'apply BC' or 'apply b->c' which lets me work backwards to b *)
  apply BC.
  (* do the same thing with AB which leaves me with 'a'*)
  apply AB.
  (* finally I apply my assumption HA ?? *)

  apply HA.
Qed.
  
  
  
  