Require Import CauchySeq.
Require Import ZArith.
Require Import Classical_Prop.

(**
* Definitions
*)

(**
** Limits of real functions
*)

Variable f : CSetoid_un_op IR.

(**
We define the limit [l] of the function [f x] as [x] approaches [x0] with 
9 different cases (depending on [l] and [x0]) :
- [x0] is finite :
  - [l] is finite :
  - [l] is +&infin; :
  - [l] is -&infin; :
- [x0] is +&infin; :
  - [l] is finite :
  - [l] is +&infin; :
  - [l] is -&infin; :
- [x0] is -&infin; :
  - [l] is finite :
  - [l] is +&infin; :
  - [l] is -&infin; :
*)

Require Import RealFuncts.

Inductive limit : Type :=
    | xFinite_lFinite : IR->IR->limit
    | xFinite_lPlusInf : IR->limit
    | xFinite_lMinusInf : IR->limit
    | xPlusInf_lFinite : IR->limit
    | xPlusInf_lPlusInf : limit
    | xPlusInf_lMinusInf : limit
    | xMinusInf_lFinite : IR->limit
    | xMinusInf_lPlusInf : limit
    | xMinusInf_lMinusInf : limit.

(**
We assign a predicate to each limit :
*)

Definition limitProp (L : limit) : CProp :=
    match L with
        (* This is the same definition that [funLim] in CoRN *)
        | xFinite_lFinite x0 l => forall (e : IR), e [>] [0] -> exists (d : IR), d [>] [0] 
                -> forall (x : IR), AbsSmall d (x [-] x0) -> AbsSmall e ((f x) [-] l)
        | xFinite_lPlusInf x0 => forall (A : IR), exists (d : IR), d [>] [0] 
                -> forall (x : IR), AbsSmall d (x [-] x0) -> (f x) [>=] A
        | xFinite_lMinusInf x0 => forall (A : IR), exists (d : IR), d [>] [0] 
                -> forall (x : IR), AbsSmall d (x [-] x0) -> (f x) [<=] A
        | xPlusInf_lFinite l => forall (e : IR), e [>] [0] -> exists (a : IR), 
                forall (x : IR), x [>=] a -> AbsSmall e ((f x) [-] l)
        | xPlusInf_lPlusInf => forall (A : IR), exists (a : IR),
                forall (x : IR), x [>=] a -> (f x) [>=] A
        | xPlusInf_lMinusInf => forall (A : IR), exists (a : IR),
                forall (x : IR), x [>=] a -> (f x) [<=] A
        | xMinusInf_lFinite l => forall (e : IR), e [>] [0] -> exists (a : IR),
                forall (x : IR), x [<=] a -> AbsSmall e ((f x) [-] l)
        | xMinusInf_lPlusInf => forall (A : IR), exists (a : IR),
                forall (x : IR), x [<=] a -> (f x) [>=] A
        | xMinusInf_lMinusInf => forall (A : IR), exists (a : IR),
                forall (x : IR), x [<=] a -> (f x) [<=] A
    end.

(**
* Theorems
*)

(**
Sequential characterization of a limit
*)


(**
* Applications
*)

(**
** Appli 1
*)

(**
If f is a periodic function over [IR], and f has a real limit in #+&infin;#
Then f is a constant function.
*)

(**
We use this definitions for a periodic function, and a constant function : 
*)

Definition periodic_function (T : IR) : Prop :=
    exists (k : Z), forall (x : IR), f x = f (x [+] (cr_mult (zring k) T)).

Definition constant_function : Prop :=
    forall (x y : IR), f x = f y.

Theorem app1 : forall (T : IR), periodic_function T -> 
    forall (l : IR), limitProp (xPlusInf_lFinite l) -> constant_function.
    intros. unfold constant_function. intros. apply NNPP ; intro. unfold periodic_function in H. destruct H.
    assert (f x = f (x[+]zring x0[*]T)) by apply H.
    assert (f y = f (y[+]zring x0[*]T)) by apply H.
Admitted.

(** 
** Appli 2 : Prove that a function has no limit
*)

(**
1) sin(x)
We extract the 
*) 



