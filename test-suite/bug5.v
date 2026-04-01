Declare ML Module "coq-paramcoq.plugin".

From Stdlib Require Import PeanoNat Recdef.
Set Implicit Arguments.




Fixpoint subS (n m : nat) {struct n} : nat :=
  match n return  nat with
  | 0 => 0(* originally n*)
  | S k => match m return nat with
           | 0 => S k (* originally n*)
           | S l => subS k l
           end
  end.



Definition modS :=
fun x y : nat => match y with
                 | 0 => y
                 | S y' => subS y' (snd (Nat.divmod x y' 0 y'))
                 end.

(*
Lemma subS_same : forall n m, subS  n m = Nat.sub n m.
Proof.
  induction n; destruct m; simpl; auto.
Qed.

Lemma modS_same : forall n m, modS  n m = Nat.modulo n m.
Proof.
   destruct m; simpl; auto.
    rewrite  subS_same. reflexivity.
Qed.
*)
Lemma NNmod_upper_boundA
     : forall a b : nat, b <> 0 -> modS a  b < b.
Admitted.

Definition T := forall a b : nat, b <> 0 -> modS a  b < b.
Parametricity Recursive T.
Print T_R.

Axiom NNmod_upper_boundA_R : (fun H H0 : forall a b : nat, b <> 0 -> modS a b < b =>
forall (a₁ a₂ : nat) (a_R : nat_R a₁ a₂) (b₁ b₂ : nat) (b_R : nat_R b₁ b₂)
  (H1 : b₁ <> 0) (H2 : b₂ <> 0),
not_R (eq_R nat_R b_R nat_R_O_R) H1 H2 ->
lt_R (modS_R a_R b_R) b_R (H a₁ b₁ H1)
  (H0 a₂ b₂ H2)) NNmod_upper_boundA NNmod_upper_boundA.

Realizer  NNmod_upper_boundA as NNmod_upper_boundA_RR := NNmod_upper_boundA_R.


Lemma NNmod_upper_bound
     : forall a b : nat, b <> 0 -> modS a  b < b.
Proof.
  
  intros. apply NNmod_upper_boundA. assumption.
Qed.




Function GcdS (a b : nat) {wf lt a} : nat :=
match a with
 | O => b 
 | S k =>  GcdS (modS b (S k))  (S k)
end.
Proof.
- intros m n k Heq. apply  NNmod_upper_bound.
  intros Hc. inversion Hc.
- apply Wf_nat.lt_wf.
Defined.


From Stdlib Require Import ProofIrrelevance.
Parametricity Recursive sig_rec.

Ltac destruct_reflexivity := 
  intros ; repeat match goal with 
    | [ x : _ |- _ = _ ] => destruct x; reflexivity; fail
  end.

Ltac destruct_construct x := 
    (destruct x; [ constructor 1 ]; auto; fail)
 || (destruct x; [ constructor 1 | constructor 2 ]; auto; fail)
 || (destruct x; [ constructor 1 | constructor 2 | constructor 3]; auto; fail).

Ltac unfold_cofix := intros; match goal with 
 [ |- _ = ?folded ] =>  
    let x := fresh "x" in 
    let typ := type of folded in 
    (match folded with _ _ => pattern folded | _ => pattern folded at 2 end);
    match goal with [ |- ?P ?x ] => 
    refine (let rebuild : typ -> typ := _ in 
            let path : rebuild folded = folded := _ in  
            eq_rect _ P _ folded path) end; 
    [ intro x ; destruct_construct x; fail 
    | destruct folded; reflexivity
    | reflexivity]; fail
end.

Ltac destruct_with_nat_arg_pattern x :=
  pattern x;
  match type of x with 
   | ?I 0 => refine (let gen : forall m (q : I m), 
     (match m return I m -> Type with 
         0 => fun p => _ p
     | S n => fun _  => unit end q) := _ in gen 0 x)     
   | ?I (S ?n) => refine (let gen : forall m (q : I m), 
     (match m return I m -> Type with 
         0 => fun _  => unit 
     | S n => fun p => _ p end q) := _ in gen (S n) x)
  end; intros m q; destruct q.

Ltac destruct_reflexivity_with_nat_arg_pattern := 
  intros ; repeat match goal with 
    | [ x : _ |- _ = _ ] => destruct_with_nat_arg_pattern x; reflexivity; fail
  end.
 
Global Parametricity Tactic := ((destruct_reflexivity; fail)
                            || (unfold_cofix; fail) 
                            || (destruct_reflexivity_with_nat_arg_pattern; fail)
                            ||  auto). 

Parametricity Recursive GcdS qualified.

(*
1 subgoal
______________________________________(1/1)
forall (a₁ a₂ : nat) (a_R : nat_R a₁ a₂) (b₁ b₂ : nat) (b_R : nat_R b₁ b₂),
sig_R nat_R
  (fun (v₁ v₂ : nat) (v_R : nat_R v₁ v₂) =>
   ex_R nat_R
     (fun (p₁ p₂ : nat) (p_R : nat_R p₁ p₂)
        (H : forall k : nat,
             p₁ < k ->
             forall def : nat -> nat -> nat,
             iter (nat -> nat -> nat) k GcdS_F def a₁ b₁ = v₁)
        (H0 : forall k : nat,
              p₂ < k ->
              forall def : nat -> nat -> nat,
              iter (nat -> nat -> nat) k GcdS_F def a₂ b₂ = v₂) =>
      forall (k₁ k₂ : nat) (k_R : nat_R k₁ k₂) (H1 : p₁ < k₁) (H2 : p₂ < k₂),
      Coq__o__Init__o__Peano__o__lt_R p_R k_R H1 H2 ->
      forall (def₁ def₂ : nat -> nat -> nat)
        (def_R : forall a₁0 a₂0 : nat,
                 nat_R a₁0 a₂0 ->
                 forall b₁0 b₂0 : nat,
                 nat_R b₁0 b₂0 -> nat_R (def₁ a₁0 b₁0) (def₂ a₂0 b₂0)),
      eq_R nat_R
        (Coq__o__funind__o__Recdef__o__iter_R
           (fun H3 H4 : nat -> nat -> nat =>
            forall a₁0 a₂0 : nat,
            nat_R a₁0 a₂0 ->
            forall b₁0 b₂0 : nat,
            nat_R b₁0 b₂0 -> nat_R (H3 a₁0 b₁0) (H4 a₂0 b₂0)) k_R GcdS_F
           GcdS_F Top__o__GcdS_F_R def₁ def₂ def_R a₁ a₂ a_R b₁ b₂ b_R) v_R
        (H k₁ H1 def₁) (H0 k₂ H2 def₂))) (GcdS_terminate a₁ b₁)
  (GcdS_terminate a₂ b₂)
*)

(*
DepRefs:
GcdS_F
iter
and
iff
Basics.impl
unit
Init.Unconvertible
Relation_Definitions.relation
Morphisms.Proper
RelationClasses.subrelation
Morphisms.subrelation_proper
eq_rect
eq_ind
eq_sym
eq_ind_r
PeanoNat.Nat.succ_wd_obligation_1
PeanoNat.Nat.succ_wd
Morphisms.subrelation_refl
Morphisms.respectful
RelationClasses.Transitive
RelationClasses.transitivity
Morphisms.trans_co_impl_morphism_obligation_1
Morphisms.trans_co_impl_morphism
RelationClasses.Symmetric
RelationClasses.Reflexive
RelationClasses.Equivalence
RelationClasses.Equivalence_Transitive
RelationClasses.PER
RelationClasses.PER_Symmetric
RelationClasses.symmetry
RelationClasses.PER_Transitive
Morphisms.PER_morphism_obligation_1
Morphisms.PER_morphism
Init.Nat.pred
RelationClasses.Equivalence_Symmetric
RelationClasses.Equivalence_PER
PeanoNat.Nat.pred_succ
Morphisms.reflexive_proper_proxy
and_rect
and_ind
Morphisms.iff_impl_subrelation
PeanoNat.Nat.pred_wd_obligation_1
PeanoNat.Nat.pred_wd
RelationClasses.Equivalence_Reflexive
Morphisms.subrelation_respectful
RelationClasses.eq_Reflexive
eq_trans
RelationClasses.eq_Transitive
RelationClasses.eq_Symmetric
RelationClasses.eq_equivalence
PeanoNat.Nat.eq_equiv
PeanoNat.Nat.succ_inj
PeanoNat.Nat.succ_inj_wd
Morphisms.ProperProxy
Morphisms.Reflexive_partial_app_morphism
False_rect
False_ind
iff_sym
RelationClasses.iff_Symmetric
iff_trans
RelationClasses.iff_Transitive
iff_refl
RelationClasses.iff_Reflexive
RelationClasses.iff_equivalence
Morphisms.per_partial_app_morphism_obligation_1
Morphisms.per_partial_app_morphism
Morphisms.trans_sym_co_inv_impl_morphism_obligation_1
Morphisms.trans_sym_co_inv_impl_morphism
Basics.flip
RelationClasses.reflexivity
comparison
Init.Nat.compare
or
or_ind
Morphisms.trans_co_eq_inv_impl_morphism_obligation_1
Morphisms.trans_co_eq_inv_impl_morphism
Morphisms.eq_proper_proxy
Morphisms_Prop.or_iff_morphism_obligation_1
Morphisms_Prop.or_iff_morphism
nat_rect
nat_ind
f_equal
f_equal_nat
eq_add_S
True
PeanoNat.Nat.compare_eq_iff
le_0_n
le_ind
le_pred
le_S_n
le_n_S
PeanoNat.Nat.compare_le_iff
PeanoNat.Nat.compare_lt_iff
PeanoNat.Nat.lt_eq_cases
PeanoNat.Nat.le_refl
Morphisms.iff_flip_impl_subrelation
PeanoNat.Nat.lt_succ_r
PeanoNat.Nat.lt_succ_diag_r
PeanoNat.Nat.lt_wd_obligation_1
PeanoNat.Nat.lt_wd
PeanoNat.Nat.compare_refl
Morphisms_Prop.not_iff_morphism_obligation_1
Morphisms_Prop.not_iff_morphism
PeanoNat.Nat.lt_irrefl
PeanoNat.Nat.neq_succ_diag_l
PeanoNat.Nat.lt_le_incl
PeanoNat.Nat.nlt_succ_diag_l
PeanoNat.Nat.nle_succ_diag_l
PeanoNat.Nat.bi_induction
Morphisms_Prop.iff_iff_iff_impl_morphism_obligation_1
Morphisms_Prop.iff_iff_iff_impl_morphism
PeanoNat.Nat.central_induction
PeanoNat.Nat.le_wd
or_iff_compat_r
or_cancel_r
PeanoNat.Nat.le_succ_l
PeanoNat.Nat.succ_lt_mono
Lt.lt_S_n
Acc
Acc_inv
RelationClasses.complement
RelationClasses.Irreflexive
RelationClasses.StrictOrder
RelationClasses.StrictOrder_Transitive
PeanoNat.Nat.lt_asymm
PeanoNat.Nat.lt_trans
PeanoNat.Nat.lt_strorder
PeanoNat.Nat.Private_OrderTac.IsTotal.lt_strorder
PeanoNat.Nat.le_lteq
PeanoNat.Nat.Private_OrderTac.IsTotal.le_lteq
PeanoNat.Nat.lt_compat
PeanoNat.Nat.Private_OrderTac.IsTotal.lt_compat
OrdersTac.ord
OrdersTac.trans_ord
PeanoNat.Nat.Private_OrderTac.IsTotal.eq_equiv
PeanoNat.Nat.Private_OrderTac.Tac.interp_ord
PeanoNat.Nat.Private_OrderTac.Tac.trans
PeanoNat.Nat.Private_OrderTac.Tac.le_lt_trans
RelationClasses.StrictOrder_Irreflexive
PeanoNat.Nat.Private_OrderTac.Tac.lt_irrefl
PeanoNat.Nat.le_gt_cases
PeanoNat.Nat.lt_trichotomy
PeanoNat.Nat.lt_total
PeanoNat.Nat.Private_OrderTac.IsTotal.lt_total
PeanoNat.Nat.Private_OrderTac.Tac.not_ge_lt
PeanoNat.Nat.lt_le_trans
Wf_nat.ltof
Lt.lt_n_Sm_le
PeanoNat.Nat.Private_OrderTac.Tac.lt_eq
PeanoNat.Nat.Private_OrderTac.Tac.not_gt_le
PeanoNat.Nat.eq_le_incl
PeanoNat.Nat.Private_OrderTac.Tac.lt_trans
PeanoNat.Nat.le_le_succ_r
PeanoNat.Nat.le_succ_r
PeanoNat.Nat.pred_0
PeanoNat.Nat.neq_succ_0
PeanoNat.Nat.le_0_l
PeanoNat.Nat.le_ngt
PeanoNat.Nat.nlt_0_r
well_founded
Wf_nat.well_founded_ltof
Wf_nat.lt_wf
NNmod_upper_bound
GcdS_tcc
max_type
max_type_rect
max_type_ind
ex
ex_ind
Lt.lt_n_S
nat_rec
gt
Lt.lt_le_S
Gt.gt_le_S
all
Morphisms.pointwise_relation
Morphisms_Prop.all_iff_morphism_obligation_1
Morphisms_Prop.all_iff_morphism
PeanoNat.Nat.lt_exists_pred_strong
PeanoNat.Nat.lt_exists_pred
PeanoNat.Nat.rs_rs'
PeanoNat.Nat.A'A_right
PeanoNat.Nat.rbase
PeanoNat.Nat.lt_lt_succ_r
PeanoNat.Nat.rs'_rs''
PeanoNat.Nat.strong_right_induction
PeanoNat.Nat.right_induction
PeanoNat.Nat.induction
PeanoNat.Nat.lt_0_succ
Le.le_n_S
sumbool
sumbool_rect
sumbool_rec
Compare_dec.le_lt_dec
Compare_dec.le_gt_dec
max
and_rec
PeanoNat.Nat.le_lt_trans
GcdS_terminate
GcdS
Top__o__GcdS_F_R is defined
'Top__o__GcdS_F_R' is now a registered translation.
Coq__o__funind__o__Recdef__o__iter_R is defined
'Coq__o__funind__o__Recdef__o__iter_R' is now a registered translation.
and_R is defined
and_R_rect is defined
and_R_ind is defined
and_R_rec is defined
Coq__o__Init__o__Logic__o__iff_R is defined
'Coq__o__Init__o__Logic__o__iff_R' is now a registered translation.
Coq__o__Program__o__Basics__o__impl_R is defined
'Coq__o__Program__o__Basics__o__impl_R' is now a registered translation.
unit_R is defined
unit_R_rect is defined
unit_R_ind is defined
unit_R_rec is defined
Coq__o__Classes__o__Init__o__Unconvertible_R is defined
'Coq__o__Classes__o__Init__o__Unconvertible_R' is now a registered translation.
Coq__o__Relations__o__Relation_Definitions__o__relation_R is defined
'Coq__o__Relations__o__Relation_Definitions__o__relation_R' is now a registered translation.
Coq__o__Classes__o__Morphisms__o__Proper_R is defined
'Coq__o__Classes__o__Morphisms__o__Proper_R' is now a registered translation.
Coq__o__Classes__o__RelationClasses__o__subrelation_R is defined
'Coq__o__Classes__o__RelationClasses__o__subrelation_R' is now a registered translation.
Coq__o__Classes__o__Morphisms__o__subrelation_proper_R is defined
'Coq__o__Classes__o__Morphisms__o__subrelation_proper_R' is now a registered translation.
Coq__o__Init__o__Logic__o__eq_rect_R is defined
'Coq__o__Init__o__Logic__o__eq_rect_R' is now a registered translation.
Coq__o__Init__o__Logic__o__eq_ind_R is defined
'Coq__o__Init__o__Logic__o__eq_ind_R' is now a registered translation.
Coq__o__Init__o__Logic__o__eq_sym_R is defined
'Coq__o__Init__o__Logic__o__eq_sym_R' is now a registered translation.
Coq__o__Init__o__Logic__o__eq_ind_r_R is defined
'Coq__o__Init__o__Logic__o__eq_ind_r_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__succ_wd_obligation_1_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__succ_wd_obligation_1_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__succ_wd_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__succ_wd_R' is now a registered translation.
Coq__o__Classes__o__Morphisms__o__subrelation_refl_R is defined
'Coq__o__Classes__o__Morphisms__o__subrelation_refl_R' is now a registered translation.
Coq__o__Classes__o__Morphisms__o__respectful_R is defined
'Coq__o__Classes__o__Morphisms__o__respectful_R' is now a registered translation.
Coq__o__Classes__o__RelationClasses__o__Transitive_R is defined
'Coq__o__Classes__o__RelationClasses__o__Transitive_R' is now a registered translation.
Coq__o__Classes__o__RelationClasses__o__transitivity_R is defined
'Coq__o__Classes__o__RelationClasses__o__transitivity_R' is now a registered translation.
Coq__o__Classes__o__Morphisms__o__trans_co_impl_morphism_obligation_1_R is defined
'Coq__o__Classes__o__Morphisms__o__trans_co_impl_morphism_obligation_1_R' is now a registered translation.
Coq__o__Classes__o__Morphisms__o__trans_co_impl_morphism_R is defined
'Coq__o__Classes__o__Morphisms__o__trans_co_impl_morphism_R' is now a registered translation.
Coq__o__Classes__o__RelationClasses__o__Symmetric_R is defined
'Coq__o__Classes__o__RelationClasses__o__Symmetric_R' is now a registered translation.
Coq__o__Classes__o__RelationClasses__o__Reflexive_R is defined
'Coq__o__Classes__o__RelationClasses__o__Reflexive_R' is now a registered translation.
Equivalence_R is defined
Coq__o__Classes__o__RelationClasses__o__Equivalence_Transitive_R is defined
'Coq__o__Classes__o__RelationClasses__o__Equivalence_Transitive_R' is now a registered translation.
PER_R is defined
Coq__o__Classes__o__RelationClasses__o__PER_Symmetric_R is defined
'Coq__o__Classes__o__RelationClasses__o__PER_Symmetric_R' is now a registered translation.
Coq__o__Classes__o__RelationClasses__o__symmetry_R is defined
'Coq__o__Classes__o__RelationClasses__o__symmetry_R' is now a registered translation.
Coq__o__Classes__o__RelationClasses__o__PER_Transitive_R is defined
'Coq__o__Classes__o__RelationClasses__o__PER_Transitive_R' is now a registered translation.
Coq__o__Classes__o__Morphisms__o__PER_morphism_obligation_1_R is defined
'Coq__o__Classes__o__Morphisms__o__PER_morphism_obligation_1_R' is now a registered translation.
Coq__o__Classes__o__Morphisms__o__PER_morphism_R is defined
'Coq__o__Classes__o__Morphisms__o__PER_morphism_R' is now a registered translation.
Coq__o__Init__o__Nat__o__pred_R is defined
'Coq__o__Init__o__Nat__o__pred_R' is now a registered translation.
Coq__o__Classes__o__RelationClasses__o__Equivalence_Symmetric_R is defined
'Coq__o__Classes__o__RelationClasses__o__Equivalence_Symmetric_R' is now a registered translation.
Coq__o__Classes__o__RelationClasses__o__Equivalence_PER_R is defined
'Coq__o__Classes__o__RelationClasses__o__Equivalence_PER_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__pred_succ_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__pred_succ_R' is now a registered translation.
Coq__o__Classes__o__Morphisms__o__reflexive_proper_proxy_R is defined
'Coq__o__Classes__o__Morphisms__o__reflexive_proper_proxy_R' is now a registered translation.
Coq__o__Init__o__Logic__o__and_rect_R is defined
'Coq__o__Init__o__Logic__o__and_rect_R' is now a registered translation.
Coq__o__Init__o__Logic__o__and_ind_R is defined
'Coq__o__Init__o__Logic__o__and_ind_R' is now a registered translation.
Coq__o__Classes__o__Morphisms__o__iff_impl_subrelation_R is defined
'Coq__o__Classes__o__Morphisms__o__iff_impl_subrelation_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__pred_wd_obligation_1_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__pred_wd_obligation_1_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__pred_wd_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__pred_wd_R' is now a registered translation.
Coq__o__Classes__o__RelationClasses__o__Equivalence_Reflexive_R is defined
'Coq__o__Classes__o__RelationClasses__o__Equivalence_Reflexive_R' is now a registered translation.
Coq__o__Classes__o__Morphisms__o__subrelation_respectful_R is defined
'Coq__o__Classes__o__Morphisms__o__subrelation_respectful_R' is now a registered translation.
Coq__o__Classes__o__RelationClasses__o__eq_Reflexive_R is defined
'Coq__o__Classes__o__RelationClasses__o__eq_Reflexive_R' is now a registered translation.
Coq__o__Init__o__Logic__o__eq_trans_R is defined
'Coq__o__Init__o__Logic__o__eq_trans_R' is now a registered translation.
Coq__o__Classes__o__RelationClasses__o__eq_Transitive_R is defined
'Coq__o__Classes__o__RelationClasses__o__eq_Transitive_R' is now a registered translation.
Coq__o__Classes__o__RelationClasses__o__eq_Symmetric_R is defined
'Coq__o__Classes__o__RelationClasses__o__eq_Symmetric_R' is now a registered translation.
Coq__o__Classes__o__RelationClasses__o__eq_equivalence_R is defined
'Coq__o__Classes__o__RelationClasses__o__eq_equivalence_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__eq_equiv_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__eq_equiv_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__succ_inj_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__succ_inj_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__succ_inj_wd_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__succ_inj_wd_R' is now a registered translation.
Coq__o__Classes__o__Morphisms__o__ProperProxy_R is defined
'Coq__o__Classes__o__Morphisms__o__ProperProxy_R' is now a registered translation.
Coq__o__Classes__o__Morphisms__o__Reflexive_partial_app_morphism_R is defined
'Coq__o__Classes__o__Morphisms__o__Reflexive_partial_app_morphism_R' is now a registered translation.
Coq__o__Init__o__Logic__o__False_rect_R is defined
'Coq__o__Init__o__Logic__o__False_rect_R' is now a registered translation.
Coq__o__Init__o__Logic__o__False_ind_R is defined
'Coq__o__Init__o__Logic__o__False_ind_R' is now a registered translation.
Coq__o__Init__o__Logic__o__iff_sym_R is defined
'Coq__o__Init__o__Logic__o__iff_sym_R' is now a registered translation.
Coq__o__Classes__o__RelationClasses__o__iff_Symmetric_R is defined
'Coq__o__Classes__o__RelationClasses__o__iff_Symmetric_R' is now a registered translation.
Coq__o__Init__o__Logic__o__iff_trans_R is defined
'Coq__o__Init__o__Logic__o__iff_trans_R' is now a registered translation.
Coq__o__Classes__o__RelationClasses__o__iff_Transitive_R is defined
'Coq__o__Classes__o__RelationClasses__o__iff_Transitive_R' is now a registered translation.
Coq__o__Init__o__Logic__o__iff_refl_R is defined
'Coq__o__Init__o__Logic__o__iff_refl_R' is now a registered translation.
Coq__o__Classes__o__RelationClasses__o__iff_Reflexive_R is defined
'Coq__o__Classes__o__RelationClasses__o__iff_Reflexive_R' is now a registered translation.
Coq__o__Classes__o__RelationClasses__o__iff_equivalence_R is defined
'Coq__o__Classes__o__RelationClasses__o__iff_equivalence_R' is now a registered translation.
Coq__o__Classes__o__Morphisms__o__per_partial_app_morphism_obligation_1_R is defined
'Coq__o__Classes__o__Morphisms__o__per_partial_app_morphism_obligation_1_R' is now a registered translation.
Coq__o__Classes__o__Morphisms__o__per_partial_app_morphism_R is defined
'Coq__o__Classes__o__Morphisms__o__per_partial_app_morphism_R' is now a registered translation.
Coq__o__Classes__o__Morphisms__o__trans_sym_co_inv_impl_morphism_obligation_1_R is defined
'Coq__o__Classes__o__Morphisms__o__trans_sym_co_inv_impl_morphism_obligation_1_R' is now a registered translation.
Coq__o__Classes__o__Morphisms__o__trans_sym_co_inv_impl_morphism_R is defined
'Coq__o__Classes__o__Morphisms__o__trans_sym_co_inv_impl_morphism_R' is now a registered translation.
Coq__o__Program__o__Basics__o__flip_R is defined
'Coq__o__Program__o__Basics__o__flip_R' is now a registered translation.
Coq__o__Classes__o__RelationClasses__o__reflexivity_R is defined
'Coq__o__Classes__o__RelationClasses__o__reflexivity_R' is now a registered translation.
comparison_R is defined
comparison_R_rect is defined
comparison_R_ind is defined
comparison_R_rec is defined
Coq__o__Init__o__Nat__o__compare_R is defined
'Coq__o__Init__o__Nat__o__compare_R' is now a registered translation.
or_R is defined
or_R_ind is defined
Coq__o__Init__o__Logic__o__or_ind_R is defined
'Coq__o__Init__o__Logic__o__or_ind_R' is now a registered translation.
Coq__o__Classes__o__Morphisms__o__trans_co_eq_inv_impl_morphism_obligation_1_R is defined
'Coq__o__Classes__o__Morphisms__o__trans_co_eq_inv_impl_morphism_obligation_1_R' is now a registered translation.
Coq__o__Classes__o__Morphisms__o__trans_co_eq_inv_impl_morphism_R is defined
'Coq__o__Classes__o__Morphisms__o__trans_co_eq_inv_impl_morphism_R' is now a registered translation.
Coq__o__Classes__o__Morphisms__o__eq_proper_proxy_R is defined
'Coq__o__Classes__o__Morphisms__o__eq_proper_proxy_R' is now a registered translation.
Coq__o__Classes__o__Morphisms_Prop__o__or_iff_morphism_obligation_1_R is defined
'Coq__o__Classes__o__Morphisms_Prop__o__or_iff_morphism_obligation_1_R' is now a registered translation.
Coq__o__Classes__o__Morphisms_Prop__o__or_iff_morphism_R is defined
'Coq__o__Classes__o__Morphisms_Prop__o__or_iff_morphism_R' is now a registered translation.
Coq__o__Init__o__Datatypes__o__nat_rect_R is defined
'Coq__o__Init__o__Datatypes__o__nat_rect_R' is now a registered translation.
Coq__o__Init__o__Datatypes__o__nat_ind_R is defined
'Coq__o__Init__o__Datatypes__o__nat_ind_R' is now a registered translation.
Coq__o__Init__o__Logic__o__f_equal_R is defined
'Coq__o__Init__o__Logic__o__f_equal_R' is now a registered translation.
Coq__o__Init__o__Peano__o__f_equal_nat_R is defined
'Coq__o__Init__o__Peano__o__f_equal_nat_R' is now a registered translation.
Coq__o__Init__o__Peano__o__eq_add_S_R is defined
'Coq__o__Init__o__Peano__o__eq_add_S_R' is now a registered translation.
True_R is defined
True_R_rect is defined
True_R_ind is defined
True_R_rec is defined
Coq__o__Arith__o__PeanoNat__o__Nat__o__compare_eq_iff_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__compare_eq_iff_R' is now a registered translation.
Coq__o__Init__o__Peano__o__le_0_n_R is defined
'Coq__o__Init__o__Peano__o__le_0_n_R' is now a registered translation.
Coq__o__Init__o__Peano__o__le_ind_R is defined
'Coq__o__Init__o__Peano__o__le_ind_R' is now a registered translation.
Coq__o__Init__o__Peano__o__le_pred_R is defined
'Coq__o__Init__o__Peano__o__le_pred_R' is now a registered translation.
Coq__o__Init__o__Peano__o__le_S_n_R is defined
'Coq__o__Init__o__Peano__o__le_S_n_R' is now a registered translation.
Coq__o__Init__o__Peano__o__le_n_S_R is defined
'Coq__o__Init__o__Peano__o__le_n_S_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__compare_le_iff_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__compare_le_iff_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__compare_lt_iff_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__compare_lt_iff_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_eq_cases_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_eq_cases_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__le_refl_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__le_refl_R' is now a registered translation.
Coq__o__Classes__o__Morphisms__o__iff_flip_impl_subrelation_R is defined
'Coq__o__Classes__o__Morphisms__o__iff_flip_impl_subrelation_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_succ_r_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_succ_r_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_succ_diag_r_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_succ_diag_r_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_wd_obligation_1_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_wd_obligation_1_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_wd_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_wd_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__compare_refl_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__compare_refl_R' is now a registered translation.
Coq__o__Classes__o__Morphisms_Prop__o__not_iff_morphism_obligation_1_R is defined
'Coq__o__Classes__o__Morphisms_Prop__o__not_iff_morphism_obligation_1_R' is now a registered translation.
Coq__o__Classes__o__Morphisms_Prop__o__not_iff_morphism_R is defined
'Coq__o__Classes__o__Morphisms_Prop__o__not_iff_morphism_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_irrefl_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_irrefl_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__neq_succ_diag_l_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__neq_succ_diag_l_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_le_incl_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_le_incl_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__nlt_succ_diag_l_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__nlt_succ_diag_l_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__nle_succ_diag_l_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__nle_succ_diag_l_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__bi_induction_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__bi_induction_R' is now a registered translation.
Coq__o__Classes__o__Morphisms_Prop__o__iff_iff_iff_impl_morphism_obligation_1_R is defined
'Coq__o__Classes__o__Morphisms_Prop__o__iff_iff_iff_impl_morphism_obligation_1_R' is now a registered translation.
Coq__o__Classes__o__Morphisms_Prop__o__iff_iff_iff_impl_morphism_R is defined
'Coq__o__Classes__o__Morphisms_Prop__o__iff_iff_iff_impl_morphism_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__central_induction_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__central_induction_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__le_wd_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__le_wd_R' is now a registered translation.
Coq__o__Init__o__Logic__o__or_iff_compat_r_R is defined
'Coq__o__Init__o__Logic__o__or_iff_compat_r_R' is now a registered translation.
Coq__o__Init__o__Logic__o__or_cancel_r_R is defined
'Coq__o__Init__o__Logic__o__or_cancel_r_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__le_succ_l_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__le_succ_l_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__succ_lt_mono_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__succ_lt_mono_R' is now a registered translation.
Coq__o__Arith__o__Lt__o__lt_S_n_R is defined
'Coq__o__Arith__o__Lt__o__lt_S_n_R' is now a registered translation.
Acc_R is defined
Acc_R_rect is defined
Acc_R_ind is defined
Acc_R_rec is defined
Coq__o__Init__o__Wf__o__Acc_inv_R is defined
'Coq__o__Init__o__Wf__o__Acc_inv_R' is now a registered translation.
Coq__o__Classes__o__RelationClasses__o__complement_R is defined
'Coq__o__Classes__o__RelationClasses__o__complement_R' is now a registered translation.
Coq__o__Classes__o__RelationClasses__o__Irreflexive_R is defined
'Coq__o__Classes__o__RelationClasses__o__Irreflexive_R' is now a registered translation.
StrictOrder_R is defined
Coq__o__Classes__o__RelationClasses__o__StrictOrder_Transitive_R is defined
'Coq__o__Classes__o__RelationClasses__o__StrictOrder_Transitive_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_asymm_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_asymm_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_trans_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_trans_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_strorder_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_strorder_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__Private_OrderTac__o__IsTotal__o__lt_strorder_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__Private_OrderTac__o__IsTotal__o__lt_strorder_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__le_lteq_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__le_lteq_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__Private_OrderTac__o__IsTotal__o__le_lteq_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__Private_OrderTac__o__IsTotal__o__le_lteq_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_compat_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_compat_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__Private_OrderTac__o__IsTotal__o__lt_compat_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__Private_OrderTac__o__IsTotal__o__lt_compat_R' is now a registered translation.
ord_R is defined
ord_R_rect is defined
ord_R_ind is defined
ord_R_rec is defined
Coq__o__Structures__o__OrdersTac__o__trans_ord_R is defined
'Coq__o__Structures__o__OrdersTac__o__trans_ord_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__Private_OrderTac__o__IsTotal__o__eq_equiv_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__Private_OrderTac__o__IsTotal__o__eq_equiv_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__Private_OrderTac__o__Tac__o__interp_ord_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__Private_OrderTac__o__Tac__o__interp_ord_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__Private_OrderTac__o__Tac__o__trans_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__Private_OrderTac__o__Tac__o__trans_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__Private_OrderTac__o__Tac__o__le_lt_trans_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__Private_OrderTac__o__Tac__o__le_lt_trans_R' is now a registered translation.
Coq__o__Classes__o__RelationClasses__o__StrictOrder_Irreflexive_R is defined
'Coq__o__Classes__o__RelationClasses__o__StrictOrder_Irreflexive_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__Private_OrderTac__o__Tac__o__lt_irrefl_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__Private_OrderTac__o__Tac__o__lt_irrefl_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__le_gt_cases_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__le_gt_cases_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_trichotomy_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_trichotomy_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_total_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_total_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__Private_OrderTac__o__IsTotal__o__lt_total_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__Private_OrderTac__o__IsTotal__o__lt_total_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__Private_OrderTac__o__Tac__o__not_ge_lt_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__Private_OrderTac__o__Tac__o__not_ge_lt_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_le_trans_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_le_trans_R' is now a registered translation.
Coq__o__Arith__o__Wf_nat__o__ltof_R is defined
'Coq__o__Arith__o__Wf_nat__o__ltof_R' is now a registered translation.
Coq__o__Arith__o__Lt__o__lt_n_Sm_le_R is defined
'Coq__o__Arith__o__Lt__o__lt_n_Sm_le_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__Private_OrderTac__o__Tac__o__lt_eq_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__Private_OrderTac__o__Tac__o__lt_eq_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__Private_OrderTac__o__Tac__o__not_gt_le_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__Private_OrderTac__o__Tac__o__not_gt_le_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__eq_le_incl_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__eq_le_incl_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__Private_OrderTac__o__Tac__o__lt_trans_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__Private_OrderTac__o__Tac__o__lt_trans_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__le_le_succ_r_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__le_le_succ_r_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__le_succ_r_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__le_succ_r_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__pred_0_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__pred_0_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__neq_succ_0_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__neq_succ_0_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__le_0_l_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__le_0_l_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__le_ngt_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__le_ngt_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__nlt_0_r_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__nlt_0_r_R' is now a registered translation.
Coq__o__Init__o__Wf__o__well_founded_R is defined
'Coq__o__Init__o__Wf__o__well_founded_R' is now a registered translation.
Coq__o__Arith__o__Wf_nat__o__well_founded_ltof_R is defined
'Coq__o__Arith__o__Wf_nat__o__well_founded_ltof_R' is now a registered translation.
Coq__o__Arith__o__Wf_nat__o__lt_wf_R is defined
'Coq__o__Arith__o__Wf_nat__o__lt_wf_R' is now a registered translation.
Top__o__NNmod_upper_bound_R is defined
'Top__o__NNmod_upper_bound_R' is now a registered translation.
Top__o__GcdS_tcc_R is defined
'Top__o__GcdS_tcc_R' is now a registered translation.
max_type_R is defined
max_type_R_rect is defined
max_type_R_ind is defined
max_type_R_rec is defined
Coq__o__funind__o__Recdef__o__max_type_rect_R is defined
'Coq__o__funind__o__Recdef__o__max_type_rect_R' is now a registered translation.
Coq__o__funind__o__Recdef__o__max_type_ind_R is defined
'Coq__o__funind__o__Recdef__o__max_type_ind_R' is now a registered translation.
ex_R is defined
ex_R_ind is defined
Coq__o__Init__o__Logic__o__ex_ind_R is defined
'Coq__o__Init__o__Logic__o__ex_ind_R' is now a registered translation.
Coq__o__Arith__o__Lt__o__lt_n_S_R is defined
'Coq__o__Arith__o__Lt__o__lt_n_S_R' is now a registered translation.
Coq__o__Init__o__Datatypes__o__nat_rec_R is defined
'Coq__o__Init__o__Datatypes__o__nat_rec_R' is now a registered translation.
Coq__o__Init__o__Peano__o__gt_R is defined
'Coq__o__Init__o__Peano__o__gt_R' is now a registered translation.
Coq__o__Arith__o__Lt__o__lt_le_S_R is defined
'Coq__o__Arith__o__Lt__o__lt_le_S_R' is now a registered translation.
Coq__o__Arith__o__Gt__o__gt_le_S_R is defined
'Coq__o__Arith__o__Gt__o__gt_le_S_R' is now a registered translation.
Coq__o__Init__o__Logic__o__all_R is defined
'Coq__o__Init__o__Logic__o__all_R' is now a registered translation.
Coq__o__Classes__o__Morphisms__o__pointwise_relation_R is defined
'Coq__o__Classes__o__Morphisms__o__pointwise_relation_R' is now a registered translation.
Coq__o__Classes__o__Morphisms_Prop__o__all_iff_morphism_obligation_1_R is defined
'Coq__o__Classes__o__Morphisms_Prop__o__all_iff_morphism_obligation_1_R' is now a registered translation.
Coq__o__Classes__o__Morphisms_Prop__o__all_iff_morphism_R is defined
'Coq__o__Classes__o__Morphisms_Prop__o__all_iff_morphism_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_exists_pred_strong_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_exists_pred_strong_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_exists_pred_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_exists_pred_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__rs_rs'_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__rs_rs'_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__A'A_right_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__A'A_right_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__rbase_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__rbase_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_lt_succ_r_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_lt_succ_r_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__rs'_rs''_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__rs'_rs''_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__strong_right_induction_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__strong_right_induction_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__right_induction_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__right_induction_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__induction_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__induction_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_0_succ_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__lt_0_succ_R' is now a registered translation.
Coq__o__Arith__o__Le__o__le_n_S_R is defined
'Coq__o__Arith__o__Le__o__le_n_S_R' is now a registered translation.
sumbool_R is defined
sumbool_R_rect is defined
sumbool_R_ind is defined
sumbool_R_rec is defined
Coq__o__Init__o__Specif__o__sumbool_rect_R is defined
'Coq__o__Init__o__Specif__o__sumbool_rect_R' is now a registered translation.
Coq__o__Init__o__Specif__o__sumbool_rec_R is defined
'Coq__o__Init__o__Specif__o__sumbool_rec_R' is now a registered translation.
Coq__o__Arith__o__Compare_dec__o__le_lt_dec_R is defined
'Coq__o__Arith__o__Compare_dec__o__le_lt_dec_R' is now a registered translation.
Coq__o__Arith__o__Compare_dec__o__le_gt_dec_R is defined
'Coq__o__Arith__o__Compare_dec__o__le_gt_dec_R' is now a registered translation.
Coq__o__funind__o__Recdef__o__max_R is defined
'Coq__o__funind__o__Recdef__o__max_R' is now a registered translation.
Coq__o__Init__o__Logic__o__and_rec_R is defined
'Coq__o__Init__o__Logic__o__and_rec_R' is now a registered translation.
Coq__o__Arith__o__PeanoNat__o__Nat__o__le_lt_trans_R is defined
'Coq__o__Arith__o__PeanoNat__o__Nat__o__le_lt_trans_R' is now a registered translation.

Anomaly: Uncaught exception Not_found. Please report at
http://coq.inria.fr/bugs/.
*)
