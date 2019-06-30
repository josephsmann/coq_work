Theorem EM_0 : forall A: Prop, ~ (A /\ ~A).
Proof.
intro A.
unfold not.
intro H.
elim H.
intros.
pose (proof_of_False := H1 H0).
exact proof_of_False.
Qed.

Theorem TF : forall A: Prop, (A -> False)->True.
Proof.
tauto.
Qed.

Theorem EM_1 : forall A: Prop, ( ~A \/ A).
Proof.
intro A.
tauto.
