Inductive bits : Type :=
  | E
  | O (s : bits)
  | Z (s : bits).

Fixpoint equ_bits (s t:bits) : Prop :=
  match s with
  | E => match t with
    | E => True
    | O t' => False
    | Z t' => False
    end
  | O s' => match t with
    | E => False
    | O t' => equ_bits s' t'
    | Z t' => False
    end
  | Z s' => match t with
    | E => False
    | O t' => False
    | Z t' => equ_bits s' t'
    end
  end.

Compute equ_bits (O E) (O E).

Check equ_bits.

Fixpoint len_bits (s :bits) : nat :=
  match s with
  | E => 0
  | O s' => 1 + len_bits s'
  | Z s' => 1 + len_bits s'
  end.

Theorem len_0_bits: len_bits E = 0.
Proof.
trivial.
Qed.

Theorem impl1: E = E.
Proof.
trivial.
Qed.

Lemma impl1n: E <> E -> False.
Proof.
intros H.
unfold not in H.
case H.
trivial.
Qed.

Theorem len_2_bits: forall s : bits,
s <> E -> exists t : bits, s = (O t) \/ s = (Z t).
Proof.
intros s.
unfold not.
destruct s.
  -intros H.

  pose (witness := E ).
  refine (ex_intro _ witness _).
  apply impl1 in H.

  pose (proof_of_f := H impl1).
  exact proof_of_f.

Qed.

Theorem len_1_bits: forall s : bits,
(len_bits (O s) > 0) /\ (len_bits (Z s) > 0).
Proof.
induction s.
Qed.

Compute len_bits E.
Compute len_bits (O (Z E)).

Check bits_ind.

Theorem Th0: forall s : bits,
s <> E -> len_bits s <> 0.
Proof.
intros s.
intros H.
unfold not in H.
destruct s.
  - intros H1.
  - .

  - intros H1.


Qed.

Theorem Th1: forall s t : bits, 
len_bits s <> len_bits t -> not (equ_bits s t).
Proof.
intros s.
elim s.
  intros t. 
  intros H.
  unfold len_bits.
Qed.
