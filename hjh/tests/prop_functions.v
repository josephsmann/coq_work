Require Import PeanoNat.
Local Open Scope nat_scope.
Check nat_ind.
Check eq.
Fixpoint eq_nat n m : Prop :=
  match n, m with
    | O, O => True
    | O, S _ => False
    | S _, O => False
    | S n1, S m1 => eq_nat n1 m1
  end.

Compute eq_nat 3 4.

Theorem T1: forall x:nat, eq_nat x x.
Proof.
induction x.
unfold eq_nat.
exact I.
unfold eq_nat.


