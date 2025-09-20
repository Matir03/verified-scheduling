From Coq Require Import Reals.
From Coq Require Import ZArith.
From Coq Require Import Strings.String.
(* From Coq Require Import Lists.List. *)
From Coq Require Import Program.Basics.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import vcfloat.VCFloat

From Examples Require Import Matmul.
From Inferpad Require Import Reify.
From Lower Require Import ATLDeep Sexpr Zexpr.
From ATL Require Import Map Sets FrapWithoutSets Div Tactics.
From Lower Require Import ListMisc Range Constant.
(* Import ListNotations. *)

Section Examples.

Variables a b c : Z.

Definition Z0 := ZLit 0.

Definition matmul_expr: ATLexpr :=
    Gen "i" Z0 (|a|)%z (
        Gen "j" Z0 (|b|)%z (
            Sum "k" Z0 (|c|)%z (
                Scalar (Mul (Get "A" [!"i"!; !"k"!])
                            (Get "B" [!"k"!; !"j"!]))%z
            )
        )
    ).

(* Compute (sizeof matmul_expr). *)

End Examples.

Section Tensors.

Inductive Tensor (T : Type) :=
    | Elem (t : T)
    | Conc (l : list (Tensor T)).

Fixpoint tensor_map {A B : Type} (f : A -> B) (t : Tensor A) : Tensor B :=
    match t with
    | Elem _ a => Elem _ (f a)
    | Conc _ l => Conc _ (map (tensor_map f) l)
    end.

Section Map2.

Context {A B C : Type} (f : A -> B -> C).

Fixpoint map2 (l1 : list A) (l2 : list B) : list C :=
    match l1, l2 with
    | [], [] => []
    | a :: l1, b :: l2 => f a b :: map2 l1 l2
    | _, _ => []
    end.

End Map2.

Fixpoint tensor_map2 {A B C : Type} (f : A -> B -> C) (t1 : Tensor A) (t2 : Tensor B) : Tensor C :=
    match t1, t2 with
    | Elem _ a, Elem _ b => Elem _ (f a b)
    | Conc _ l1, Conc _ l2 => Conc _ (map2 (tensor_map2 f) l1 l2)
    | _, _ => Conc _ []
    end.
End Tensors.

(*
Definition tensor_sum2 (t1 t2 : Tensor Sexpr) : Tensor Sexpr :=
    (tensor_map2 Add t1 t2).

Fixpoint tensor_sum (l : list (Tensor Sexpr)) : Tensor Sexpr :=
    match l with
    | [] => Conc _ []
    | h :: [] => h
    | h :: t => tensor_sum2 h (tensor_sum t)
    end.
*)

Definition list_gen {T : Type} (lo hi : Z) (f : Z -> T) : list T :=
    map (fun i => f ((Z.of_nat i + lo)%Z)) (seq 0 (Z.to_nat (hi - lo))).

Definition index_lists (lo hi : Z) (vi : string) (indices : valuation) : list valuation :=
    (list_gen lo hi (fun i => indices $+ (vi, i))).

Definition extract (z : option Z) : Zexpr :=
    match z with
    | Some z => ZLit z
    | None => ZVar "#error: unbound index"
    end.

Fixpoint eval_vars (e : Sexpr) (vars : valuation) : Sexpr :=
    match e with
    | Get v i => Get v (map extract (map (eval_Zexpr_Z vars) i))
    | Lit _ | Var _ => e
    | Mul s1 s2 => Mul (eval_vars s1 vars) (eval_vars s2 vars)
    | Sub s1 s2 => Sub (eval_vars s1 vars) (eval_vars s2 vars)
    | Div s1 s2 => Div (eval_vars s1 vars) (eval_vars s2 vars)
    | Sexpr.Add s1 s2 => Sexpr.Add (eval_vars s1 vars) (eval_vars s2 vars)
    end.

Definition reduce {A B : Type} (f : A -> B -> A) (l : list B) (b: B -> A) (c : A) : A :=
    match l with
    | x :: xs => fold_left f xs (b x)
    | [] => c
    end.

Fixpoint pointwise_expr_with_indices (e : ATLexpr) (indices : valuation) : (Tensor Sexpr) :=
    match e with
    | Scalar s => Elem _ (eval_vars s indices)
    | Gen vi (ZLit lo) (ZLit hi) body =>
        Conc _ (map (pointwise_expr_with_indices body) (index_lists lo hi vi indices))
    | Sum vi (ZLit lo) (ZLit hi) (Scalar s) =>
        Elem _
        (reduce
            (fun s1 vars => Sexpr.Add s1 (eval_vars s vars))
            (index_lists lo hi vi indices)
            (eval_vars s)
            (Lit 0))
    | _ => Conc _ []
    end.

Check matmul_expr.

Compute pointwise_expr_with_indices (matmul_expr 1 1 1) $0.
