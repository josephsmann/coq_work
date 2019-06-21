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

  
  