Require Import ZArith.
Require Import Classical_Prop.

Require Import SAMPL.sequences.

(**
* Definitions
*)

Section Limit_definitions.

(**
** Limits of real functions
*)

Variable f : CSetoid_un_op IR.

(**
We define the limit [l] of the function [f x] as [x] approaches [x0] with 
9 different cases (depending on [l] and [x0]) :
- [x0] is finite :
  - [l] is finite : $$x_0 \in \mathbb{R}, \lim\limits_{x \to x_0} f(x) = l \in \mathbb{R}$$
  - [l] is $$+\infty$$ : $$x_0 \in \mathbb{R}, \lim\limits_{x \to x_0} f(x) = +\infty$$
  - [l] is $$-\infty$$ : $$x_0 \in \mathbb{R}, \lim\limits_{x \to x_0} f(x) = -\infty$$
- [x0] is $$+\infty$$ :
  - [l] is finite : $$\lim\limits_{x \to +\infty} f(x) = l \in \mathbb{R}$$
  - [l] is $$+\infty$$ : $$\lim\limits_{x \to +\infty} f(x) = +\infty$$
  - [l] is $$-\infty$$ : $$\lim\limits_{x \to +\infty} f(x) = -\infty$$
- [x0] is $$-\infty$$ :
  - [l] is finite : $$\lim\limits_{x \to -\infty} f(x) = l \in \mathbb{R}$$
  - [l] is $$+\infty$$ : $$\lim\limits_{x \to -\infty} f(x) = +\infty$$
  - [l] is $$-\infty$$ : $$\lim\limits_{x \to -\infty} f(x) = -\infty$$
*)

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
- [x0] is finite :
  - [l] is finite : $$\forall \epsilon>0, \exists \delta>0, \forall x \in \[x_0 - \delta, x_0 + \delta\] \cap I, |f(x)-l| \leq \epsilon$$
  - [l] is $$+\infty$$ : $$\forall A \in \mathbb{R}, \exists \delta>0, \forall x \in \[x_0 - \delta, x_0 + \delta\] \cap I, f(x) \geq A$$
  - [l] is $$-\infty$$ : $$\forall A \in \mathbb{R}, \exists \delta>0, \forall x \in \[x_0 - \delta, x_0 + \delta\] \cap I, f(x) \leq A$$
- [x0] is $$+\infty$$ :
  - [l] is finite : $$\forall \epsilon>0, \exists a \in \mathbb{R}, \forall x \in I, x \geq a \Rightarrow |f(x)-l| \leq \epsilon$$
  - [l] is $$+\infty$$ : $$\forall A \in \mathbb{R}, \exists a \in \mathbb{R}, \forall x \in I, x \geq a \Rightarrow f(x) \geq A$$
  - [l] is $$-\infty$$ : $$\forall A \in \mathbb{R}, \exists a \in \mathbb{R}, \forall x \in I, x \geq a \Rightarrow f(x) \leq A$$
- [x0] is $$-\infty$$ :
  - [l] is finite : $$\forall \epsilon>0, \exists a \in \mathbb{R}, \forall x \in I, x \leq a \Rightarrow |f(x)-l| \leq \epsilon$$
  - [l] is $$+\infty$$ : $$\forall A \in \mathbb{R}, \exists a \in \mathbb{R}, \forall x \in I, x \leq a \Rightarrow f(x) \geq A$$
  - [l] is $$-\infty$$ : $$\forall A \in \mathbb{R}, \exists a \in \mathbb{R}, \forall x \in I, x \leq a \Rightarrow f(x) \leq A$$
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
In the previous definitions, $$x_0 \in \overline{\mathbb{R}}$$ and $$l \in \overline{\mathbb{R}}$$, so we
define to helper definitions to deal with them as [IR_inf] :
*)

Definition limit_variable (L : limit) : IR_inf :=
    match L with
        | xFinite_lFinite x0 _ => real x0
        | xFinite_lPlusInf x0 => real x0
        | xFinite_lMinusInf x0 => real x0
        | xPlusInf_lFinite _ => pInf
        | xPlusInf_lPlusInf => pInf
        | xPlusInf_lMinusInf => pInf
        | xMinusInf_lFinite _ => mInf
        | xMinusInf_lPlusInf => mInf
        | xMinusInf_lMinusInf => mInf
    end.

Definition limit_value (L : limit) : IR_inf :=
    match L with
        | xFinite_lFinite _ l => real l
        | xFinite_lPlusInf _ => pInf
        | xFinite_lMinusInf _ => mInf
        | xPlusInf_lFinite l => real l
        | xPlusInf_lPlusInf => pInf
        | xPlusInf_lMinusInf => mInf
        | xMinusInf_lFinite l => real l
        | xMinusInf_lPlusInf => pInf
        | xMinusInf_lMinusInf => mInf
    end.

(**
* Theorems
*)

(**
Sequential characterization of a limit
*)

End Limit_definitions.

Hypothesis x0 : IR_inf.
Hypothesis l : IR_inf.
Hypothesis f : CSetoid_un_op IR.

Theorem sequential_limit : (forall (L : limit), limitProp f L -> limit_variable L = x0 -> limit_value L = l)
    <-> (forall (Un : nat->IR), forall (L fL : Un_limit), Un_limitProp Un L -> Un_limitProp (fun n => f (Un n)) fL 
        -> Un_limit_value L = x0 -> Un_limit_value fL = l).
Admitted.

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

(*Theorem app1 : forall (T : IR), periodic_function T -> 
    forall (l : IR), limitProp (xPlusInf_lFinite l) -> constant_function.
    intros. unfold constant_function. intros. apply NNPP ; intro. unfold periodic_function in H. destruct H.
    assert (f x = f (x[+]zring x0[*]T)) by apply H.
    assert (f y = f (y[+]zring x0[*]T)) by apply H.
Admitted.*)

(** 
** Appli 2 : Prove that a function has no limit
*)

(**
1) sin(x)
We extract the 
*)



