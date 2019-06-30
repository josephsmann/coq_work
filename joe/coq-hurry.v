(* Coq Hurry *)
(* answers at the end *)


Require Import List. (* needed for list operations *)

Fixpoint nlist n := 
match n with
  0 => nil
  | S 0 => nil
  | S p => nlist p ++ (p :: nil)
end.

Compute nlist 3.

Lemma E1p24:  (forall A B C:Prop, A/\(B/\C)->(A/\B)/\C).
Proof.
  intros.
  split.
  destruct H as [a [b c]].
  - split.
    + exact a.
    + exact b.
  - destruct H as [a [b c]].
exact c.
Show Proof.
Qed.

Lemma E1p24f:  (forall A B C:Prop, A/\(B/\C)->(A/\B)/\C).
Proof.
  exact (fun (A B C: Prop)(H: A/\(B/\C)) =>
conj
  match H with
    | conj a (conj b c) => conj a b
  end
  match H with
    | conj a (conj b c) => c
  end).
Qed.

(* Lemma E1p24f: (forall A B C:Prop, A/\(B/\C)->(A/\B)/\C).
Proof.
exact (fun A B C:Prop H:A/\(B/\C) =>  *)

Goal (forall A B C D: Prop,(A->B)/\(C->D)/\A/\C -> B/\D).
Proof.
  intros.
  destruct H as [I1 [I2 [a c]]].
  split.
  exact (I1 a).
  exact (I2 c).
  Show Proof.
Qed.

Goal (forall A B C D: Prop,(A->B)/\(C->D)/\A/\C -> B/\D).
Proof.
  exact 
    (fun (A B C D: Prop) (H : (A->B) /\ (C->D) /\ A /\ C ) =>
    match H with
      | conj I1 (conj I2 (conj a c)) =>  conj (I1 a) (I2 c)
    end).
Qed.

Goal (forall A: Prop, ~(A/\~A)).
Proof.
  intros.
  intro.
  destruct H as [AT AF].
  exact (AF AT).
  Show Proof.
Qed.

(* Check and Print are your friends.. *)
Check and_ind.
Print and_ind.

Goal (forall A: Prop, ~(A/\~A)).
Proof.
exact
  (fun (A: Prop)(T : (A /\~A)) =>
  match T with
  | conj a na => (na a)
  end).
Qed.


Goal (forall A B C: Prop, A\/(B\/C)->(A\/B)\/C).
  intros.
  destruct H as [a | [b | c]].
  left. left. exact a.
  left. right. exact b.
  right. exact c.
  Show Proof.
Qed.


Inductive prb: Type :=
  Lp: prb
| Mp: nat -> prb -> prb
| Np: bool -> prb -> prb -> prb.

Check Lp.
Check  Mp 3 Lp .
Check Np true (Mp 3 (Mp 4 Lp)) Lp.

Inductive p1 : Type :=
  p : p1
|  P : p1 -> p1.
(* | Q : p1 -> prb. *)

Check P p.
Check P( P p).



Inductive bin : Type :=
  L : bin
| N: bin -> bin -> bin.


Goal (forall A B: Prop, (A\/B)/\~A -> B).
  intros.
  destruct H as [avb na].
  destruct avb as [a | bb].
  destruct na. (* THIS. false -> anything so the new goal is A. if A then anything then B *)
  exact a.
  exact bb.
  Show Proof.
Qed.

Goal (forall A B: Prop,  (A\/B)/\~A -> B).
Proof.
exact 
  (fun (A B: Prop) (H:  (A\/B)/\~A) =>
    match H with 
      | conj (or_introl a) na => 
          match (na a) return B with end  (* what kind of wacky voodoo is this?? *)
      | conj (or_intror b) na => b
    end).
Qed.
 

Print Nat.

(* Require Import Ring. *)
Goal (forall x:nat, 2 * x = x + x).
Proof.
induction x.
simpl.
reflexivity.
SearchRewrite (_ * S _).
unfold Nat.mul .
SearchRewrite(_ + 0).
rewrite <- plus_n_O .
reflexivity.
Show Proof.
Qed.

(*
 (fun x : nat =>
 nat_ind 
    (fun x0 : nat => 2 * x0 = x0 + x0) 
    eq_refl
   (fun (x0 : nat) (_ : 2 * x0 = x0 + x0) =>
        eq_ind 
          (S x0) 
          (fun n : nat => S x0 + n = S x0 + S x0) 
          eq_refl 
          (S x0 + 0) 
          (plus_n_O (S x0))) 
 x)
 
 *)

Print nat_ind. (*  3 args: P: nat->Prop, f:P 0, f0: forall n P n -> P S n *)
Print eq_ind. (* 3 args   : forall (A : Type) (x : A) (P : A -> Prop), P x -> forall y : A, x = y -> P y*)
Print eq_ind.
(*
eq_ind = 
fun (A : Type) (x : A) (P : A -> Prop) (f : P x) (y : A) (e : x = y) =>
match e in (_ = y0) return (P y0) with
| eq_refl => f
end
     : forall (A : Type) (x : A) (P : A -> Prop), P x -> forall y : A, x = y -> P y

Argument A is implicit
Argument scopes are [type_scope _ function_scope _ _ _]
*) 

Check nat_ind.
Check eq_ind.



Check Set.


Print Nat.


 Print Nat.eqb.
(* example with
let 
*)

Open Scope nat_scope.

Locate "_ >= _".



Fixpoint count (n: nat) (l: list nat) :=
  match n, l with
    _ , nil => 0
  | n, a::tl => if Nat.eqb a n then S (count n tl) else count n tl
  end.

Fixpoint count2 (n: nat) (l: list nat) :=
  match n, l with
    _ , nil => 0
  | n, a::tl =>
     match Nat.eqb a n with
      | true => S (count n tl)
      | false =>  count n tl
    end
  end.
  
Inductive trr: Type :=
  lf: trr
| node: trr -> trr -> trr.

(* Inductive ttt: Type :=
  llf: (trr, nat)
  | nnode : (trr, nat) -> (trr, nat) -> (trr, nat).
 *)

Check lf.
Check node  lf lf.
Check node (node (node lf (node lf lf)) lf) lf.

(* Fixpoint th (l: list bool) :=
  match l with
    nil => (t, nil)
|    _ ::  nil => (t, nil)
|    _ _ :: nil => (t, nil)
|   1 0 0 :: nil => (node lf lf, nil)
|   1 0 0 :: tl => let child, _  = th tl in (node (node lf lf) child, nil)
|   1 0 1 :: tl =>  let child, _ in  (node lf child, nil)
|   1 1 0 :: tl =>let child, _ = th tl in  (node child lf, nil)
|   1 1 1 :: tl => let (leftchild, rightlist) = th tl in 
                              let (rightchild, _) = th rightlist in 
                                  (node leftchild rightchild, nil) 
                                  
                                  
Observation:
tree rep 
1's extend to left
0' take us to parent right if on left child
0's take us to last right empty node

markov matrix
from -> to
left, 0 -> sib right
left, 1 -> child left
right, 0 -> parent right
right, 1 -> child left
*)

(*  flatten_aux takes two trees and separates t1 into t_1 and t_2 and makes 
descends to make left most leaf the left leaf of the root.

 *)
Fixpoint flatten_aux (t1 t2:bin) : bin :=
  match t1 with
    L => N L t2
  | N t_1 t_2 => flatten_aux t_1 (flatten_aux t_2 t2)
  end.

Fixpoint flatten (t:bin) : bin :=
  match t with
    L => L 
    | N t1 t2 => flatten_aux t1 (flatten t2)
  end.

Fixpoint size (t:bin) : nat :=
  match t with
    L => 1 | N t1 t2 => 1 + size t1 + size t2
  end.
Compute flatten_aux (N L L) L.
Compute flatten_aux (N L L) (N L L).
Compute flatten_aux (N (N L L) L) (N (N L L) L).
  
Compute flatten (N L L).
Compute flatten ( N (N L L) (N L L)).
Compute flatten (N (N (N L L) L) (N (N L L) L)).

Compute size  (N (N (N L L) L) (N (N L L) L)).
(* you can "pick up" a tree from any point, and its still a tree... *)
Compute size (flatten (N (N (N L L) L) (N (N L L) L))).


Fixpoint lcon (n: nat) :=
match n with
  | 0 => 0 :: nil
  | S n => (S n) :: (lcon n)
end.

Compute lcon 10.

(* Fixpoint lcon (l: list nat) :=
match l with
  | nil => lf
  | 0 :: tl => node (tcon tl)
  | _ :: tl => 
end. *)

Fixpoint mt (t: bin) :=
  match t with
  | L => false::nil
  | N l r => true :: (mt l) ++ (mt r)
  end.

Compute mt  (N (N (N L L) L) (N (N L L) L)).
Compute mt (N L L).

(* Check (N L N L L).
 *)

Print bool.
Print False_ind.

Print False_ind.
Check False.
Check not True.




(* Notation
"A -> B" := forall _ : A, B : type_scope (default interpretation) 
*)

Fixpoint isBinTree (l : list bool) :=
match l with
  | nil => true
  | true :: nil => false
  | false :: nil => true
  | true :: false :: false :: nil => true
  | true :: true :: false :: nil => true
  | false : tl => 

(* idea: have function return 
Fixpoint tm (l: list bool) (rest: list bool) :=
  match l with 
    | nil => (lf, rest)
    | false :: nil => (lf, rest)
    | false :: tl => (lf , tl)
    | true :: tl => 
       match tl with 
       | false :: false :: ttl => node lf lf
       | false :: true :: ttl =>
      let (leftchild, rest1) := (tm tl rest) in
      let (rightchild, rest2) := (tm rest1 rest1) in 
          (node leftchild rightchild, nil)
  end.
end
                                  
                                  
                                  
                                  
                                  
                                  
                                  

    false::false::tl => leaf
    


 




  
  