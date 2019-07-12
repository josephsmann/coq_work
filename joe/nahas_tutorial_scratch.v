Theorem backward_large : (forall A B C : Prop,
 A -> (A->B) -> (B->C) -> C).
Proof.
 intros A B C.
 intros proof_of_A A_implies_B B_implies_C.
 refine (B_implies_C _).
   refine (A_implies_B _).
     exact proof_of_A.
Qed.

Theorem backward_huge : (forall A B C : Prop, 
    A -> (A->B) -> (A->B->C) -> C).
Proof.
 intros A B C.
 intros proof_of_A A_implies_B A_imp_B_imp_C.
 refine (A_imp_B_imp_C _ _ ).
   exact proof_of_A.

   refine (A_implies_B _ ).
     exact proof_of_A.
Qed.

Theorem forward_huge : (forall A B C : Prop, 
    A -> (A->B) -> (A->B->C) -> C).
Proof.
 intros A B C.
 intros proof_of_A A_implies_B A_imp_B_imp_C.
 pose (proof_of_B := A_implies_B proof_of_A).
 pose (proof_of_C := A_imp_B_imp_C proof_of_A proof_of_B).
 exact proof_of_C.
Show Proof.
Qed.

Theorem X: True.
Proof.
  exact I.
Qed.

Print bool.

Theorem False_cannot_be_proven : ~False.
Proof.
  unfold not.
  intros proof_of_False.
  exact proof_of_False.
Qed.

Theorem False_cannot_be_proven__again : ~False.
Proof.
  intros proof_of_False.
  case proof_of_False.
Qed.

Theorem T1: forall A : Prop, A \/ ~A -> True.
Proof.
intros A.
intros H.
elim H.
  intros.
  exact I.

  intros.
  exact I.
Qed.

Theorem absurd2 : forall A C : Prop, 
  A -> ~ A -> C.
Proof.
  intros A C.
  intros proof_of_A proof_that_A_cannot_be_proven.
  unfold not in proof_that_A_cannot_be_proven.
  pose (proof_of_False := proof_that_A_cannot_be_proven proof_of_A).
  case proof_of_False.
  Show Proof.
Qed.
(* 
(fun (A C : Prop)
   (proof_of_A : A)
   (proof_that_A_cannot_be_proven : 
    ~ A) =>
 let proof_of_False :
   False :=
     proof_that_A_cannot_be_proven proof_of_A 
 in
 match
   proof_of_False
   return C
 with
 end)
*)



Require Import Bool.

Theorem true_is_True: Is_true true.
Proof.
  simpl.
  exact I.
Qed.

Theorem not_eqb_true_false: ~(Is_true (eqb true false)).
Proof.
  simpl.
  exact False_cannot_be_proven.
Qed.

Theorem eqb_a_a : (forall a : bool, Is_true (eqb a a)).
Proof.
  intros a.
  case a.
    (** suppose a is true *)
    simpl.
    exact I.

    (** suppose a is false *)
    simpl.
    exact I.
Qed.

Theorem thm_eqb_a_t: (forall a:bool, 
    (Is_true (eqb a true)) -> (Is_true a)).
Proof.
  intros a.
  case a.
    (** suppose a is true *)
    simpl.
    intros proof_of_True.
    exact I.

    (** suppose a is false *)
    simpl.
    intros proof_of_False.
    case proof_of_False.
Qed.


(* HJH case analysis *)

Theorem T2: forall A1 A2 C : Prop, 
(A1 -> C) /\ (A2 -> C) -> (A1 \/ A2 -> C).
Proof.
intros A1 A2 C.
intros Cases.
elim Cases.
intros Case1 Case2.
intros Select.
case Select.
exact Case1.
exact Case2.
Show Proof.
(*
(fun (A1 A2 C : Prop)
   (Cases : (A1 -> C) /\
            (A2 -> C)) =>
 and_ind
   (fun (Case1 : A1 -> C)
      (Case2 : A2 -> C)
      (Select : A1 \/ A2)
    =>
    match Select with
    | or_introl x =>
        Case1 x
    | or_intror x =>
        Case2 x
    end) Cases)
*)
Qed.

Check and_ind.

Theorem T2a: forall A1 A2 C : Prop, 
(A1 -> C) /\ (A2 -> C) -> (A1 \/ A2 -> C).
Proof.
intros.

case H0.
(* elim .. intros .. -- does essentially the same thing as destruct *)
  elim H.

  intros.
  refine (H1 _).
  exact H3.

  elim H.
  intros.
  refine (H2 _).
  exact H3.

Show Proof.
(*
(fun (A1 A2 C : Prop)
   (H : (A1 -> C) /\
        (A2 -> C))
   (H0 : A1 \/ A2) =>
 match H0 with
 | or_introl x =>
     and_ind
       (fun
          (H1 : A1 -> C)
          (_ : A2 -> C)
          (H3 : A1) =>
        H1 H3) H x
 | or_intror x =>
     and_ind
       (fun (_ : A1 -> C)
          (H2 : A2 -> C)
          (H3 : A2) =>
        H2 H3) H x
 end)
*)
Qed.

Theorem T2aj: forall A1 A2 C : Prop, 
(A1 -> C) /\ (A2 -> C) -> (A1 \/ A2 -> C).
Proof.
  intros.
  destruct H as [Imp1 Imp2].
  destruct H0 as [a1 | a2].
  exact (Imp1 a1).
  exact (Imp2 a2).
  Show Proof.
(*   (fun (A1 A2 C : Prop) (H : (A1 -> C) /\ (A2 -> C)) (H0 : A1 \/ A2) =>
 match H with
 | conj Imp1 Imp2 => match H0 with
                     | or_introl a1 => Imp1 a1
                     | or_intror a2 => Imp2 a2
                     end
 end) *)
Qed.

Theorem T3: forall A B: Prop, A /\ B -> B.
Proof.
intros A B.
intros Conj.
destruct Conj as [L R].
Show Proof.
exact R.
Show Proof.
(*
(fun (A B : Prop) (Conj : A /\ B) =>
 match Conj with
 | conj _ R => R
 end)
*)
Qed.



Check and_ind.

Theorem T3a: forall A B: Prop, A /\ B -> B.
Proof.
intros A B.
Show Proof.
intros Conj.
elim Conj.
Show Proof.
intros.
Show Proof.
exact H0.
Show Proof.
(*
(fun (A B : Prop) (Conj : A /\ B) =>
 and_ind (fun (_ : A) (H0 : B) => H0) Conj)
*)

Qed.

Print and_ind.

(*
and_ind = 
fun (A B P : Prop) (f : A -> B -> P) (a : A /\ B) =>
match a with
| conj x x0 => f x x0
end
     : forall A B P : Prop, (A -> B -> P) -> A /\ B -> P

Arguments A, B, P are implicit
Argument scopes are [type_scope type_scope type_scope
  function_scope _]

*)

(* or *)
Theorem left_or : (forall A B : Prop, A -> A \/ B).
Proof.
  intros A B.
  intros proof_of_A.
  pose (proof_of_A_or_B := or_introl proof_of_A: A \/ B).
  exact proof_of_A_or_B.
  Show Proof.
(*   (fun (A B : Prop) (proof_of_A : A) =>
 let proof_of_A_or_B : A \/ B := or_introl proof_of_A : A \/ B in proof_of_A_or_B) *)
Qed.

Goal (forall A B: Prop, A -> A \/ B).
Proof.
  exact (fun (a b: Prop) (Pa: a) => or_introl Pa).
Qed.

Print or_introl.

Theorem right_or : (forall A B : Prop, B -> A \/ B).
Proof.
  intros A B.
  intros proof_of_B.
  refine (or_intror _).
    exact proof_of_B.
Qed.

Theorem right_or_1 : (forall A B : Prop, B -> A \/ B).
Proof.
  intros A B.
  intros proof_of_B.
  exact ( or_intror proof_of_B ).
Qed.

Theorem or_commutes : (forall A B, A \/ B -> B \/ A).
Proof.
  intros A B.
  intros A_or_B.
  case A_or_B.
(* suppose A_or_B is (or_introl proof_of_A) *)
    intros proof_of_A.
    refine (or_intror _).
      exact proof_of_A.

(* suppose A_or_B is (or_intror proof_of_B) *)
    intros proof_of_B.
    refine (or_introl _).
      exact proof_of_B.
Qed.


Theorem both_and : (forall A B : Prop, A -> B -> A /\ B).
Proof.
  intros A B.
  intros proof_of_A proof_of_B.
  refine (conj _ _).
    exact proof_of_A.

    exact proof_of_B.
Qed.

Theorem both_and_1 : (forall A B : Prop, A -> B -> A /\ B).
Proof.
  intros A B.
  intros proof_of_A proof_of_B.
  exact (conj proof_of_A proof_of_B).
Qed.

Theorem and_commutes : (forall A B, A /\ B -> B /\ A).
Proof.
  intros A B.
  intros A_and_B.
  case A_and_B.
  (* suppose A_and_B is (conj proof_of_A proof_of_B) *)
    intros proof_of_A proof_of_B.
    refine (conj _ _).
      exact proof_of_B.

      exact proof_of_A.
Qed.

Theorem and_commutes__again : (forall A B, A /\ B -> B /\ A).
Proof.
  intros A B.
  intros A_and_B.
  destruct A_and_B as [ proof_of_A proof_of_B].
  refine (conj _ _). (* or split *)
    exact proof_of_B.

    exact proof_of_A.
Qed.

Theorem and_commutes__again1 : (forall A B, A /\ B -> B /\ A).
Proof.
  intros A B.
  intros A_and_B.
  destruct A_and_B as [ proof_of_A proof_of_B].
  exact (conj proof_of_B proof_of_A).
Qed.

Infix "&&" := andb : bool_scope.
Infix "||" := orb : bool_scope.

Print "&&".

Definition ifff (A B:Prop) := (A -> B) /\ (B -> A).

Print "<->".

Definition stupid (A B : Prop) := ifff A B.

(* 
Goal  forall A: Prop, stupid A A.
Proof.
intros A.
unfold stupid. 
unfold ifff.
*)


Compute orb true false.

(* Notation "A <-> B" := (iff A B) : type_scope. *)

Print True.

Theorem orb_is_or : (forall a b, Is_true (orb a b) <-> Is_true a \/ Is_true b).
Proof.
  intros a b.
  unfold iff.
  Show Proof.
  refine (conj _ _).
    (** orb -> \/ *)
    intros H.
    case a, b.
      (** suppose a,b is true, true *)
      simpl.
      refine (or_introl _).
        exact I.

      (** suppose a,b is true, false *)
      simpl.
      exact (or_introl I).

      (** suppose a,b is false, true *)
      exact (or_intror I).

      (** suppose a,b is false, false  vacously true*)
      simpl in H.
      case H.

    (** \/ -> orb *)
    intros H.
    case a, b.
      (** suppose a,b is true, true *)
      simpl.
      exact I.

      (** suppose a,b is true, false *)
      exact I.

      (** suppose a,b is false, true *)
      exact I.

      (** suppose a,b is false, false *)
      case H.
         (** suppose H is (or_introl A) *)
         intros A.
         simpl in A.
         case A.

         (** suppose H is (or_intror B) *)
         intros B.
         simpl in B.
         case B.
Qed.


Theorem andb_is_and : (forall a b, Is_true (andb a b) <-> Is_true a /\ Is_true b).
Proof.
  intros a b.
  unfold iff.
  refine (conj _ _).
    (** andb -> /\ *)
    intros H.
    case a, b.
      (** suppose a,b is true,true *)
      simpl.
      exact (conj I I).

      (** suppose a,b is true,false *)
      simpl in H.
      case H.

      (** suppose a,b is false,true *)
      simpl in H.
      case H.

      (** suppose a,b is false,false *)
      simpl in H.
      case H.

    (** /\ -> andb *)
    intros H.
    case a,b.
      (** suppose a,b is true,true *)
      simpl.
      exact I.

      (** suppose a,b is true,false *)
      simpl in H.
      destruct H as [(**conj*) A B].
      case B.

      (** suppose a,b is false,true *)
      simpl in H.
      destruct H as [(**conj*) A B].
      case A.

      (** suppose a,b is false,false *)
      simpl in H.
      destruct H as [(**conj*) A B].
      case A.
Qed.

Theorem negb_is_not : (forall a, Is_true (negb a) <-> 
  (~(Is_true a))).
Proof.
  intros a.
  case a.

  (* is true *)
  simpl.
  unfold iff.
  unfold not.

  refine( conj _ _ ).
  tauto.
  tauto.

  (* is false *)
  simpl.
  unfold not.
  unfold iff.
  tauto.

  Show Proof.

Qed.


(*
(fun a : bool =>
 if a as b return (Is_true (negb b) <-> ~ Is_true b)
 then

  conj
    (fun (H : False) (_ : True) => False_ind False H)

    (fun H : True -> False =>
     let H0 : False := let H0 : True := I in H H0 in
     (fun H1 : False => False_ind False H1) H0)

 else
  conj
    (fun (_ : True) (H0 : False) =>
     False_ind False H0)

    (fun _ : False -> False => I))

*)

Goal forall A : Prop, A -> Is_true true.
Proof.
intro A.
intro LHS.
exact I.
Show Proof.
Qed.

Goal forall A B : Prop, A -> True.
Proof.
intro A.
intro LHS.
exact I.
Show Proof.
Qed.