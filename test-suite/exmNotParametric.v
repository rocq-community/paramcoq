From Stdlib Require Import ClassicalFacts.
Inductive False_R : False -> False -> Prop :=.

Inductive or_R (A₁ A₂ : Prop) (A_R : A₁ -> A₂ -> Prop) (B₁ B₂ : Prop)
(B_R : B₁ -> B₂ -> Prop) : A₁ \/ B₁ -> A₂ \/ B₂ -> Prop :=
    or_R_or_introl_R : forall (H : A₁) (H0 : A₂),
                       A_R H H0 ->
                       or_R A₁ A₂ A_R B₁ B₂ B_R (or_introl H) (or_introl H0)
  | or_R_or_intror_R : forall (H : B₁) (H0 : B₂),
                       B_R H H0 ->
                       or_R A₁ A₂ A_R B₁ B₂ B_R (or_intror H) (or_intror H0).

Definition not_R := 
fun (A₁ A₂ : Prop) (A_R : A₁ -> A₂ -> Prop) (H : A₁ -> False)
  (H0 : A₂ -> False) =>
forall (H1 : A₁) (H2 : A₂), A_R H1 H2 -> False_R (H H1) (H0 H2).


Lemma exmNotParam (exm : excluded_middle):
(forall (A₁ A₂ : Prop) (A_R : A₁ -> A₂ -> Prop),
or_R A₁ A₂ A_R (~ A₁) (~ A₂) (not_R A₁ A₂ A_R)
  (exm A₁) (exm A₂)) -> False.
Proof using.
  intros Hc.
  specialize (Hc True False (fun _ _ => True)).
  destruct Hc; auto.
Qed.
