Declare ML Module "coq-paramcoq.plugin".

From Stdlib Require Import PeanoNat Recdef.
Set Implicit Arguments.
From Stdlib Require Import Lia.

Fixpoint subS (n m : nat) {struct n} : nat :=
  match n return  nat with
  | 0 => 0 (* originally n*)
  | S k => match m return nat with
           | 0 => S k (* originally n*)
           | S l => subS k l
           end
  end.

Definition modS :=
fun x y : nat => match y with
                 | 0 => match (1 mod 0) with | 0 => 0 | _ => x end
                 | S y' => subS y' (snd (Nat.divmod x y' 0 y'))
                 end.

Lemma subS_same : forall n m, subS  n m = Nat.sub n m.
Proof.
  induction n; destruct m; simpl; auto.
Defined.

Lemma modS_same : forall n m, modS  n m = Nat.modulo n m.
Proof.
   destruct m; simpl; auto.
    rewrite  subS_same. reflexivity.
Defined.

Function GcdS (a b : nat) {wf lt a} : nat :=
match a with
 | O => b 
 | S k =>  GcdS (modS b (S k))  (S k)
end.
Proof.
- intros m n k Heq. rewrite modS_same.
  simpl.
  lia.
- exact Wf_nat.lt_wf.
Defined.

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

From Stdlib Require Import ProofIrrelevance.

(* Parametricity Recursive GcdS qualified. *)  (* FIXME *)



(*
DepRefs:
nat
le
lt
prod
snd
subS
Init.Nat.divmod
modS
GcdS_F
Recdef.iter
and
iff
Basics.impl
unit
Init.Unconvertible
Relation_Definitions.relation
Morphisms.Proper
RelationClasses.subrelation
Morphisms.subrelation_proper
eq
eq_rect
eq_ind
eq_sym
eq_ind_r
PeanoNat.Nat.succ_wd_obligation_1
Nat.succ_wd
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
Nat.pred_succ
Morphisms.reflexive_proper_proxy
and_rect
and_ind
Morphisms.iff_impl_subrelation
PeanoNat.Nat.pred_wd_obligation_1
Nat.pred_wd
RelationClasses.Equivalence_Reflexive
Morphisms.subrelation_respectful
RelationClasses.eq_Reflexive
eq_trans
RelationClasses.eq_Transitive
RelationClasses.eq_Symmetric
RelationClasses.eq_equivalence
Nat.eq_equiv
Nat.succ_inj
Nat.succ_inj_wd
Morphisms.ProperProxy
Morphisms.Reflexive_partial_app_morphism
False
False_rect
False_ind
not
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
Nat.compare_eq_iff
Peano.le_0_n
le_ind
Peano.le_pred
Peano.le_S_n
Peano.le_n_S
Nat.compare_le_iff
Nat.compare_lt_iff
Nat.lt_eq_cases
Nat.le_refl
Morphisms.iff_flip_impl_subrelation
Nat.lt_succ_r
Nat.lt_succ_diag_r
PeanoNat.Nat.lt_wd_obligation_1
Nat.lt_wd
Nat.compare_refl
Morphisms_Prop.not_iff_morphism_obligation_1
Morphisms_Prop.not_iff_morphism
Nat.lt_irrefl
Nat.neq_succ_diag_l
Nat.lt_le_incl
Nat.nlt_succ_diag_l
Nat.nle_succ_diag_l
Nat.bi_induction
Morphisms_Prop.iff_iff_iff_impl_morphism_obligation_1
Morphisms_Prop.iff_iff_iff_impl_morphism
Nat.central_induction
Nat.le_wd
or_iff_compat_r
or_cancel_r
Nat.le_succ_l
Nat.succ_lt_mono
lt_S_n
Acc
Acc_inv
positive
BinPosDef.Pos.succ
BinPosDef.Pos.of_succ_nat
Z
BinIntDef.Z.of_nat
Decidable.decidable
Decidable.dec_not_not
BinPosDef.Pos.pred_double
BinIntDef.Z.pred_double
BinIntDef.Z.double
BinIntDef.Z.succ_double
BinIntDef.Z.pos_sub
BinPosDef.Pos.add
BinIntDef.Z.add
Morphisms.reflexive_proper
Z.eq
Morphisms.reflexive_eq_dom_reflexive
Z.add_wd
Z.eq_equiv
BinIntDef.Z.succ
Z.succ_wd
BinIntDef.Z.pred
BinIntDef.Z.opp
BinPosDef.Pos.compare_cont
BinPosDef.Pos.compare
BinPosDef.Pos.mask
BinPosDef.Pos.double_pred_mask
BinPosDef.Pos.double_mask
BinPosDef.Pos.succ_double_mask
BinPosDef.Pos.sub_mask
Pos.mask2cmp
BinPosDef.Pos.pred
BinPosDef.Pos.pred_mask
BinPosDef.Pos.sub_mask_carry
positive_rect
positive_ind
Pos.sub_mask_carry_spec
Pos.switch_Eq
Pos.compare_cont_spec
Pos.compare_xI_xO
Pos.compare_xO_xI
Pos.compare_sub_mask
BinPosDef.Pos.add_carry
Pos.add_carry_spec
Pos.add_comm
Pos.add_1_r
Pos.add_succ_r
Pos.add_succ_l
Pos.add_1_l
Pos.add_assoc
Pos.succ_pred_double
Pos.add_xI_pred_double
Pos.SubMaskSpec
Pos.sub_mask_spec
Pos.sub_mask_nul_iff
Pos.compare_eq_iff
Pos.eq_equiv
Pos.compare_refl
Pos.sub_mask_diag
Pos.compare_xI_xI
Pos.compare_xO_xO
Pos.lt
Pos.compare_lt_iff
CompOpp
Pos.compare_cont_antisym
Pos.compare_antisym
CompOpp_involutive
CompOpp_inj
CompOpp_iff
CompareSpec
Pos.compare_spec
Pos.add_no_neutral
Pos.sub_mask_add_diag_r
ex
Pos.sub_mask_neg_iff
Pos.lt_iff_add
Pos.succ_not_1
Pos.succ_inj
Pos.add_carry_add
not_eq_sym
Pos.add_reg_r
Pos.add_reg_l
Pos.add_cancel_l
Pos.sub_mask_add_diag_l
Pos.sub_mask_add
Pos.sub_mask_pos_iff
Pos.sub_mask_pos'
Pos.sub_mask_pos
BinPosDef.Pos.sub
Pos.sub_xI_xI
Pos.sub_xI_xO
Pos.sub_xO_xI
Pos.sub_xO_xO
Z.pos_sub_spec
Z.pos_sub_diag
Z.Private_BootStrap.add_opp_diag_r
Z.pos_sub_opp
Z.Private_BootStrap.opp_add_distr
Pos.peano_rect
Pos.peano_ind
Pos.compare_succ_r
Pos.compare_succ_l
Pos.compare_succ_succ
Pos.add_compare_mono_l
Pos.add_compare_mono_r
Pos.lt_trans
Pos.add_lt_mono_l
Pos.lt_succ_diag_r
Pos.lt_add_r
Pos.sub_add
Pos.add_sub_assoc
Pos.add_lt_mono_r
Pos.sub_add_distr
Pos.add_sub
Pos.sub_sub_distr
Pos.gt
Pos.gt_lt_iff
Pos.lt_gt
Z.Private_BootStrap.pos_sub_add
Z.Private_BootStrap.opp_inj
Z.Private_BootStrap.add_comm
Z.Private_BootStrap.add_0_r
Z.Private_BootStrap.add_assoc_pos
Z.Private_BootStrap.add_assoc
Z.pred_succ
Z.pred_wd
Z.succ_inj
Z.succ_inj_wd
Z.add_succ_l
Z.add_0_l
Z.succ_pred
Z.peano_ind
Z.bi_induction
Z.add_assoc
fast_Zplus_assoc
lt_n_S
nat_rec
gt
lt_le_S
gt_le_S
all
Morphisms.pointwise_relation
Morphisms_Prop.all_iff_morphism_obligation_1
Morphisms_Prop.all_iff_morphism
RelationClasses.complement
RelationClasses.Irreflexive
RelationClasses.StrictOrder
RelationClasses.StrictOrder_Transitive
Nat.lt_asymm
Nat.lt_trans
Nat.lt_strorder
Nat.Private_OrderTac.IsTotal.lt_strorder
Nat.le_lteq
Nat.Private_OrderTac.IsTotal.le_lteq
Nat.lt_compat
Nat.Private_OrderTac.IsTotal.lt_compat
OrdersTac.ord
OrdersTac.trans_ord
Nat.Private_OrderTac.IsTotal.eq_equiv
Nat.Private_OrderTac.Tac.interp_ord
Nat.Private_OrderTac.Tac.trans
Nat.Private_OrderTac.Tac.lt_trans
RelationClasses.StrictOrder_Irreflexive
Nat.Private_OrderTac.Tac.lt_irrefl
Nat.le_gt_cases
Nat.lt_trichotomy
Nat.lt_total
Nat.Private_OrderTac.IsTotal.lt_total
Nat.Private_OrderTac.Tac.not_gt_le
Nat.le_le_succ_r
Nat.Private_OrderTac.Tac.le_lt_trans
Nat.le_succ_r
Nat.lt_exists_pred_strong
Nat.lt_exists_pred
Nat.rs_rs'
Nat.A'A_right
Nat.le_ngt
Nat.rbase
Nat.lt_lt_succ_r
Nat.rs'_rs''
Nat.strong_right_induction
Nat.right_induction
Nat.Private_OrderTac.Tac.lt_eq
Nat.eq_le_incl
Nat.pred_0
Nat.neq_succ_0
Nat.le_0_l
Nat.induction
Nat.lt_0_succ
le_n_S
sumbool
sumbool_rect
sumbool_rec
le_lt_dec
le_gt_dec
Zplus_assoc_reverse
fast_Zplus_assoc_reverse
Nat.Private_OrderTac.Tac.not_ge_lt
Nat.lt_le_trans
ltof
lt_n_Sm_le
Nat.nlt_0_r
well_founded
well_founded_ltof
lt_wf
N
BinNatDef.N.sub
Init.Nat.sub
BinNatDef.N.of_nat
Init.Nat.add
BinPosDef.Pos.iter_op
BinPosDef.Pos.to_nat
BinNatDef.N.to_nat
BinPosDef.Pos.of_nat
Pos.of_nat_succ
Pos.iter_op_succ
Nat.add_succ_l
Nat.add_0_l
PeanoNat.Nat.add_wd_obligation_1
Nat.add_wd
Nat.add_assoc
Pos2Nat.inj_succ
Nat2Pos.id
SuccNat2Pos.id_succ
Nnat.Nat2N.id
BinNatDef.N.compare
Pos2Nat.is_succ
Pos.le
Pos.le_1_l
Pos.lt_succ_r
Pos.lt_1_succ
Pos.succ_pred_or
Nat.compare_succ
Pos2Nat.inj_1
Nat.compare_antisym
Nat.compare_gt_iff
Pos2Nat.is_pos
Pos2Nat.inj_compare
Nnat.N2Nat.inj_compare
Nnat.Nat2N.inj_compare
nat_compare_le
BinIntDef.Z.of_N
nat_N_Z
BinIntDef.Z.sub
BinIntDef.Z.compare
Z.compare_sub
N.le
N2Z.inj_compare
N.compare_antisym
BinIntDef.Z.max
N2Z.inj_sub_max
N2Z.inj_sub
Nat.sub_0_r
Pos.sub_mask_neg_iff'
Pos.sub_mask_neg
Pos2Nat.inj_add
PeanoNat.Nat.sub_wd_obligation_1
Nat.sub_wd
Nat.sub_succ_r
Nat.sub_0_l
Nat.nle_succ_0
Nat.succ_le_mono
Nat.sub_succ
Nat.case_analysis
Nat.double_induction
Nat.sub_0_le
Nat.sub_diag
Nat.add_succ_r
Nat.add_0_r
Nat.add_comm
Nat.lt_ind
Nat.lt_succ_l
Nat.lt_ind_rel
Nat.sub_gt
Nat.add_pred_l
Nat.add_pred_r
Nat.add_sub_assoc
Nat.add_sub
Nat.add_sub_eq_l
Pos2Nat.inj_lt
Nnat.N2Nat.inj_sub
Pos2Nat.id
Pos2Nat.inj
Nnat.N2Nat.id
Nnat.N2Nat.inj
Nnat.Nat2N.inj_sub
Nat2Z.inj_sub
BinPosDef.Pos.mul
BinIntDef.Z.mul
Z.mul_wd
Z.Private_BootStrap.mul_1_l
Pos.mul_1_r
Pos.mul_xI_r
Pos.mul_xO_r
Pos.mul_comm
Pos.mul_add_distr_l
Pos.mul_add_distr_r
Pos.add_lt_mono
Pos.gt_lt
Pos.mul_compare_mono_l
Pos.mul_lt_mono_l
Pos.mul_sub_distr_l
Pos.mul_sub_distr_r
Pos.mul_compare_mono_r
Z.Private_BootStrap.mul_add_distr_pos
Z.Private_BootStrap.mul_0_r
Z.Private_BootStrap.mul_opp_r
Z.Private_BootStrap.mul_add_distr_r
Z.mul_succ_l
Z.add_succ_r
Z.add_0_r
Z.add_comm
Z.add_cancel_l
Z.add_cancel_r
Z.mul_0_l
Z.mul_succ_r
Z.one_succ
Z.add_1_l
Zred_factor3
fast_Zred_factor3
Z.mul_0_r
Zred_factor5
fast_Zred_factor5
Z.le
Z.lt
Z.compare_eq_iff
Z.compare_le_iff
Z.compare_lt_iff
Z.lt_eq_cases
Z.lt_wd
Z.compare_refl
Z.lt_irrefl
Z.sub_succ_r
Z.lt_succ_r
Z.lt_le_incl
Z.central_induction
Z.le_refl
Z.lt_succ_diag_r
Z.neq_succ_diag_l
Z.nlt_succ_diag_l
Z.nle_succ_diag_l
Z.le_wd
Z.le_succ_l
Z.lt_asymm
Z.lt_trans
Z.le_trans
RelationClasses.PreOrder
Z.le_preorder
RelationClasses.PreOrder_Reflexive
Nat2Z.is_nonneg
Z.mul_1_r
intro_Z
Z.pred_inj
Z.pred_inj_wd
Z.opp_wd
Z.add_pred_l
Z.opp_succ
Z.opp_0
Z.opp_add_distr
fast_Zopp_plus_distr
Z.mul_add_distr_r
Z.mul_comm
Z.mul_add_distr_l
Z.add_shuffle0
Z.add_shuffle1
Z.sub_wd
Z.sub_0_r
Z.add_pred_r
Z.add_opp_r
Z.sub_succ_l
Z.sub_diag
Z.add_opp_diag_l
Z.add_opp_diag_r
Pos2Z.opp_neg
OMEGA13
fast_OMEGA13
Z.succ_lt_mono
Z.succ_le_mono
Z.add_le_mono_l
Z.add_le_mono_r
Z.opp_pred
Z.opp_involutive
Z.opp_sub_distr
Z.sub_sub_distr
Z.sub_simpl_r
Z.le_0_sub
Z.compare_antisym
Z.ge
Z.ge_le_iff
Zge_left
Nat.lt_nge
gt_not_le
not_le_minus_0
inj_minus2
Z.add_shuffle3
fast_Zplus_permute
subS_same
Init.Nat.modulo
modS_same
ge
ex_ind
Nat.lt_decidable
dec_lt
Nat.nlt_ge
not_lt
Z.add_le_mono
Z.add_nonneg_nonneg
OMEGA2
Z.gt
inj_eq
proj1
Nat.compare_ge_iff
nat_compare_ge
Nat2Z.inj_compare
Nat2Z.inj_ge
inj_ge
nat_compare_gt
Nat2Z.inj_gt
inj_gt
Nat2Z.inj_le
inj_le
Pos2Z.inj_succ
Nat2Z.inj_succ
Z.opp_eq_mul_m1
fast_Zopp_eq_mult_neg_1
sumbool_ind
GcdS_tcc
max_type
max_type_rect
max_type_ind
max
and_rec
Nat.le_lt_trans
sig
sig_rect
sig_rec
GcdS_terminate
GcdS
nat_R is defined
nat_R_rect is defined
nat_R_ind is defined
nat_R_rec is defined
le_R is defined
le_R_ind is defined
Coq__o__Init__o__Peano__o__lt_R is defined
'Coq__o__Init__o__Peano__o__lt_R' is now a registered translation.
prod_R is defined
prod_R_rect is defined
prod_R_ind is defined
prod_R_rec is defined
Coq__o__Init__o__Datatypes__o__snd_R is defined
'Coq__o__Init__o__Datatypes__o__snd_R' is now a registered translation.
Top__o__subS_R is defined
'Top__o__subS_R' is now a registered translation.
Coq__o__Init__o__Nat__o__divmod_R is defined
'Coq__o__Init__o__Nat__o__divmod_R' is now a registered translation.
Top__o__modS_R is defined
'Top__o__modS_R' is now a registered translation.
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
eq_R is defined
eq_R_rect is defined
eq_R_ind is defined
eq_R_rec is defined
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
False_R is defined
False_R_rect is defined
False_R_ind is defined
False_R_rec is defined
Coq__o__Init__o__Logic__o__False_rect_R is defined
'Coq__o__Init__o__Logic__o__False_rect_R' is now a registered translation.
Coq__o__Init__o__Logic__o__False_ind_R is defined
'Coq__o__Init__o__Logic__o__False_ind_R' is now a registered translation.
Coq__o__Init__o__Logic__o__not_R is defined
'Coq__o__Init__o__Logic__o__not_R' is now a registered translation.
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
positive_R is defined
positive_R_rect is defined
positive_R_ind is defined
positive_R_rec is defined
Coq__o__PArith__o__BinPosDef__o__Pos__o__succ_R is defined
'Coq__o__PArith__o__BinPosDef__o__Pos__o__succ_R' is now a registered translation.
Coq__o__PArith__o__BinPosDef__o__Pos__o__of_succ_nat_R is defined
'Coq__o__PArith__o__BinPosDef__o__Pos__o__of_succ_nat_R' is now a registered translation.
Z_R is defined
Z_R_rect is defined
Z_R_ind is defined
Z_R_rec is defined
Coq__o__ZArith__o__BinIntDef__o__Z__o__of_nat_R is defined
'Coq__o__ZArith__o__BinIntDef__o__Z__o__of_nat_R' is now a registered translation.
Coq__o__Logic__o__Decidable__o__decidable_R is defined
'Coq__o__Logic__o__Decidable__o__decidable_R' is now a registered translation.
Coq__o__Logic__o__Decidable__o__dec_not_not_R is defined
'Coq__o__Logic__o__Decidable__o__dec_not_not_R' is now a registered translation.
Coq__o__PArith__o__BinPosDef__o__Pos__o__pred_double_R is defined
'Coq__o__PArith__o__BinPosDef__o__Pos__o__pred_double_R' is now a registered translation.
Coq__o__ZArith__o__BinIntDef__o__Z__o__pred_double_R is defined
'Coq__o__ZArith__o__BinIntDef__o__Z__o__pred_double_R' is now a registered translation.
Coq__o__ZArith__o__BinIntDef__o__Z__o__double_R is defined
'Coq__o__ZArith__o__BinIntDef__o__Z__o__double_R' is now a registered translation.
Coq__o__ZArith__o__BinIntDef__o__Z__o__succ_double_R is defined
'Coq__o__ZArith__o__BinIntDef__o__Z__o__succ_double_R' is now a registered translation.
Coq__o__ZArith__o__BinIntDef__o__Z__o__pos_sub_R is defined
'Coq__o__ZArith__o__BinIntDef__o__Z__o__pos_sub_R' is now a registered translation.
Coq__o__PArith__o__BinPosDef__o__Pos__o__add_R is defined
'Coq__o__PArith__o__BinPosDef__o__Pos__o__add_R' is now a registered translation.
Coq__o__ZArith__o__BinIntDef__o__Z__o__add_R is defined
'Coq__o__ZArith__o__BinIntDef__o__Z__o__add_R' is now a registered translation.
Coq__o__Classes__o__Morphisms__o__reflexive_proper_R is defined
'Coq__o__Classes__o__Morphisms__o__reflexive_proper_R' is now a registered translation.
Coq__o__ZArith__o__BinInt__o__Z__o__eq_R is defined
'Coq__o__ZArith__o__BinInt__o__Z__o__eq_R' is now a registered translation.
Coq__o__Classes__o__Morphisms__o__reflexive_eq_dom_reflexive_R is defined
'Coq__o__Classes__o__Morphisms__o__reflexive_eq_dom_reflexive_R' is now a registered translation.
Coq__o__ZArith__o__BinInt__o__Z__o__add_wd_R is defined
'Coq__o__ZArith__o__BinInt__o__Z__o__add_wd_R' is now a registered translation.
Coq__o__ZArith__o__BinInt__o__Z__o__eq_equiv_R is defined
'Coq__o__ZArith__o__BinInt__o__Z__o__eq_equiv_R' is now a registered translation.
Coq__o__ZArith__o__BinIntDef__o__Z__o__succ_R is defined
'Coq__o__ZArith__o__BinIntDef__o__Z__o__succ_R' is now a registered translation.
Coq__o__ZArith__o__BinInt__o__Z__o__succ_wd_R is defined
'Coq__o__ZArith__o__BinInt__o__Z__o__succ_wd_R' is now a registered translation.
Coq__o__ZArith__o__BinIntDef__o__Z__o__pred_R is defined
'Coq__o__ZArith__o__BinIntDef__o__Z__o__pred_R' is now a registered translation.
Coq__o__ZArith__o__BinIntDef__o__Z__o__opp_R is defined
'Coq__o__ZArith__o__BinIntDef__o__Z__o__opp_R' is now a registered translation.
Coq__o__PArith__o__BinPosDef__o__Pos__o__compare_cont_R is defined
'Coq__o__PArith__o__BinPosDef__o__Pos__o__compare_cont_R' is now a registered translation.
Coq__o__PArith__o__BinPosDef__o__Pos__o__compare_R is defined
'Coq__o__PArith__o__BinPosDef__o__Pos__o__compare_R' is now a registered translation.
mask_R is defined
mask_R_rect is defined
mask_R_ind is defined
mask_R_rec is defined
Coq__o__PArith__o__BinPosDef__o__Pos__o__double_pred_mask_R is defined
'Coq__o__PArith__o__BinPosDef__o__Pos__o__double_pred_mask_R' is now a registered translation.
Coq__o__PArith__o__BinPosDef__o__Pos__o__double_mask_R is defined
'Coq__o__PArith__o__BinPosDef__o__Pos__o__double_mask_R' is now a registered translation.
Coq__o__PArith__o__BinPosDef__o__Pos__o__succ_double_mask_R is defined
'Coq__o__PArith__o__BinPosDef__o__Pos__o__succ_double_mask_R' is now a registered translation.

Anomaly: Uncaught exception Not_found. Please report at
http://coq.inria.fr/bugs/.
*)
