(* From
https://www.seas.upenn.edu/~cis500/cis500-f13/sf/Basics.html#lab15
*)

(* num style logic *)
Definition n_not (b: nat) : nat :=
  match b with
  | 0 => 1
  | S n => 0
  end.

Definition n_is_true (b: nat) : Prop :=
  match b with 
  | 0 => False
  | S n => True
  end.

Definition n_is_false (b: nat) : Prop :=
  not ( n_is_true b).

(* Regression tests *)
Example test_01: n_is_true 1 = True.
Proof.
simpl.
reflexivity.
Qed.

Example test_02: n_is_true 2 = True.
Proof.
simpl.
reflexivity.
Qed.

Example test_03: n_is_true 0 = False.
Proof.
simpl.
reflexivity.
Qed.

Print iff.
Print "<->".

(* where the not is placed in important *)

Example test_04: forall b:nat, not (n_is_true b) <-> 
   (n_is_false b).
Proof.
intros b.
unfold n_is_false.
tauto.
Show Proof.
Qed.

Example test_05: forall b:nat,  (n_is_true b) <-> 
   not (n_is_false b).
Proof.
intros b.
unfold not.
unfold n_is_false.
unfold not.
unfold iff.
refine (conj _ _ ).
tauto.

intros LHS.
tauto.
Show Proof.
Qed.

(*
Example test_04: forall b:nat, (n_is_true b) <-> 
  not (n_is_false b).
Proof.
intros b.
case b.
simpl.
unfold iff.
refine (conj _ _).
intros LHS.
unfold not.
simpl.
intros.
exact LHS.

intros LHS.
unfold not in LHS.
pose (n_is_false 0).
exact (LHS P).
unfold n_is_false in P.
unfold n_is_true in P.
unfold not in P.

unfold iff.
destruct.
simpl.
reflexivity.
Qed.
*)
