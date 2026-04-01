Declare ML Module "coq-paramcoq.plugin".

From Stdlib Require Import PeanoNat PArith.

Print BinPosDef.Pos.sub_mask.

Fixpoint sub_mask (xx yy : positive) {struct yy} : BinPosDef.Pos.mask :=
  match xx with
  | (p~1)%positive =>
      match yy with
      | (q~1)%positive => BinPosDef.Pos.double_mask (sub_mask p q)
      | (q~0)%positive => BinPosDef.Pos.succ_double_mask (sub_mask p q)
      | 1%positive => BinPosDef.Pos.IsPos p~0
      end
  | (p~0)%positive =>
      match yy with
      | (q~1)%positive => BinPosDef.Pos.succ_double_mask (sub_mask_carry p q)
      | (q~0)%positive => BinPosDef.Pos.double_mask (sub_mask p q)
      | 1%positive => BinPosDef.Pos.IsPos (BinPosDef.Pos.pred_double p)
      end
  | 1%positive =>
      match yy with
      | (_~1)%positive => BinPosDef.Pos.IsNeg
      | (_~0)%positive => BinPosDef.Pos.IsNeg
      | 1%positive => BinPosDef.Pos.IsNul
      end
  end

with sub_mask_carry (xx yy : positive) {struct yy} : BinPosDef.Pos.mask :=
  match xx with
  | (p~1)%positive =>
      match yy with
      | (q~1)%positive => BinPosDef.Pos.succ_double_mask (sub_mask_carry p q)
      | (q~0)%positive => BinPosDef.Pos.double_mask (sub_mask p q)
      | 1%positive => BinPosDef.Pos.IsPos (BinPosDef.Pos.pred_double p)
      end
  | (p~0)%positive =>
      match yy with
      | (q~1)%positive => BinPosDef.Pos.double_mask (sub_mask_carry p q)
      | (q~0)%positive => BinPosDef.Pos.succ_double_mask (sub_mask_carry p q)
      | 1%positive => BinPosDef.Pos.double_pred_mask p
      end
  | 1%positive => BinPosDef.Pos.IsNeg
  end.

(*
Set Parametricity Debug.
*)

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

Parametricity Recursive sub_mask.
