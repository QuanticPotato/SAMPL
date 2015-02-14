Require Import ZArith.
Require Import Classical_Prop.
Require Import Rbasic_fun.

Require Export SAMPL.functions.
Open Scope R_scope.

(**
* Definitions
*)

Section Limit_definitions.

(**
** Predicate true at the neighbourhood of $$x_0$$
The predicate [P x] (defined on $$I \subset \mathbb{R}$$) is true at the neighbourhood of 
$$x_0 \in \overline{\mathbb{R}}$$ if : 
- $$x_0$$ is finite : $$\exists \delta > 0, \forall x \in \[x_0 - \delta, x_0 + \delta \] \cap I, P(x) \quad \mathrm{true}$$
- $$x_0 = +\infty$$ : $$\exists a \in \mathbb{R}, \forall x \in \[a, +\infty \[ \cap I, P(x) \quad \mathrm{true}$$
- $$x_0 = -\infty$$ : $$\exists a \in \mathbb{R}, \forall x \in \]-\infty, a\] \cap I, P(x) \quad \mathrm{true}$$
*)

Section neighbourhood_def.

Variable I : R -> Prop.

Definition predicate_neighbourhood (P : (forall x : R, I x -> Prop)) (x0 : R) : Prop :=
    forall (x0_inf : R_inf x0),
    match x0_inf with
        | xReal H => forall (Hx0 : I x0), exists (d:R), d > 0 -> forall (y : R), Rabs (y - x0) <= d -> P x0 Hx0
        | pInf H => exists (a:R), forall (x : R)(Hx : I x), x >= a -> P x Hx
        | mInf H => exists (a:R), forall (x : R)(Hx : I x), x <= a -> P x Hx
end.

End neighbourhood_def.

(**
** Limits of real functions
*)

Section limit_def.

Variable f : PartFunct R.
Let I := Dom R f.

(**
We define the limit [l] of the function [f x] as [x] approaches [x0] with 
9 different cases (depending on [l] and [x0]), and we assign a predicate to each case :
- [x0] is finite :
  - [l] is finite : $$x_0 \in \mathbb{R}, \lim\limits_{x \to x_0} f(x) = l \in \mathbb{R}$$ :
$$\forall \epsilon>0, \exists \delta>0, \forall x \in \[x_0 - \delta, x_0 + \delta\] \cap I, |f(x)-l| \leq \epsilon$$
  - [l] is $$+\infty$$ : $$x_0 \in \mathbb{R}, \lim\limits_{x \to x_0} f(x) = +\infty$$ :
$$\forall A \in \mathbb{R}, \exists \delta>0, \forall x \in \[x_0 - \delta, x_0 + \delta\] \cap I, f(x) \geq A$$
  - [l] is $$-\infty$$ : $$x_0 \in \mathbb{R}, \lim\limits_{x \to x_0} f(x) = -\infty$$ :
$$\forall A \in \mathbb{R}, \exists \delta>0, \forall x \in \[x_0 - \delta, x_0 + \delta\] \cap I, f(x) \leq A$$
- [x0] is $$+\infty$$ :
  - [l] is finite : $$\lim\limits_{x \to +\infty} f(x) = l \in \mathbb{R}$$ :
$$\forall \epsilon>0, \exists a \in \mathbb{R}, \forall x \in I, x \geq a \Rightarrow |f(x)-l| \leq \epsilon$$
  - [l] is $$+\infty$$ : $$\lim\limits_{x \to +\infty} f(x) = +\infty$$ :
$$\forall A \in \mathbb{R}, \exists a \in \mathbb{R}, \forall x \in I, x \geq a \Rightarrow f(x) \geq A$$
  - [l] is $$-\infty$$ : $$\lim\limits_{x \to +\infty} f(x) = -\infty$$ :
$$\forall A \in \mathbb{R}, \exists a \in \mathbb{R}, \forall x \in I, x \geq a \Rightarrow f(x) \leq A$$
- [x0] is $$-\infty$$ :
  - [l] is finite : $$\lim\limits_{x \to -\infty} f(x) = l \in \mathbb{R}$$ :
$$\forall \epsilon>0, \exists a \in \mathbb{R}, \forall x \in I, x \leq a \Rightarrow |f(x)-l| \leq \epsilon$$
  - [l] is $$+\infty$$ : $$\lim\limits_{x \to -\infty} f(x) = +\infty$$ :
$$\forall A \in \mathbb{R}, \exists a \in \mathbb{R}, \forall x \in I, x \leq a \Rightarrow f(x) \geq A$$
  - [l] is $$-\infty$$ : $$\lim\limits_{x \to -\infty} f(x) = -\infty$$ :
$$\forall A \in \mathbb{R}, \exists a \in \mathbb{R}, \forall x \in I, x \leq a \Rightarrow f(x) \leq A$$
(We use [predicate_neighbourhood] to match [x0]).
*)

Definition limit (x0 l : R) :=
    forall (l_inf : R_inf l),
    match l_inf with
        | xReal H => predicate_neighbourhood I (fun (x:R)(Hx: Dom R f x) => forall (e : R), e > 0 -> Rabs ((f x Hx) - l) <= e) x0
        | pInf H => predicate_neighbourhood I (fun (x:R)(Hx: Dom R f x) => forall (A : R), (f x Hx) >= A) x0
        | mInf H => predicate_neighbourhood I (fun (x:R)(Hx: Dom R f x) => forall (A : R), (f x Hx) <= A) x0
    end.

End limit_def.

(**
We also define one-sided limits (When x_0 \in \mathbb{R}) : 
- When $x$ approach $x_0$ from above (right) :
$\lim\limits_{x \to x_0^+} f(x) = \left. \lim\limits_{x_0} f \right|_{I \cap ] x_0, +\infty[} = l$
- When $x$ approach $x_0$ from below (left) :
$\lim\limits_{x \to x_0^-} f(x) = \left. \lim\limits_{x_0} f \right|_{I \cap ] -\infty, x_0[} = l$
*)

Section limit_one_sided_def.

Definition limitAbove (f : PartFunct R)(x0 l : R) : Prop :=
    real x0 -> limit (restriction R f (fun (x:R) => x > x0)) x0 l.

Definition limitBelow (f : PartFunct R)(x0 l : R) : Prop :=
    real x0 -> limit (restriction R f (fun (x:R) => x < x0)) x0 l.


End limit_one_sided_def.

(**
* Theorems
*)

(**
Sequential characterization of a limit
*)

End Limit_definitions.


(**
* Theorems
*)

Section Limit_theorems.

Hypothesis x0 : IR_inf.
Hypothesis l l' : IR_inf.
Hypothesis f : CSetoid_un_op IR.
Hypothesis u v w : CSetoid_un_op IR.
Hypothesis lr : IR.

Theorem sequential_limit : (forall (L : limit), limitProp f L -> limit_variable L = x0 -> limit_value L = l)
    <-> (forall (Un : nat->IR), forall (L fL : Un_limit), Un_limitProp Un L -> Un_limitProp (fun n => f (Un n)) fL 
        -> Un_limit_value L = x0 -> Un_limit_value fL = l).
Admitted.

Theorem inequality_limit : forall (L L' : limit), limitProp u L -> limitProp v L' 
    -> predicate_neighbourhood (fun x => (u x) [<=] (v x)) x0 -> le_IR_inf l l'.
Admitted.

Theorem squeeze_theorem : (u --x0-->lr) -> (v --x0-->lr)
    -> predicate_neighbourhood (fun x => ((u x) [<=] (v x)) /\ ((v x) [<=] (w x))) x0
    -> (v --x0-->lr).
Admitted.

End Limit_theorems.

(**
* Applications
*)

(**
** Appli 1
*)

Section Appli1.

Variable f : CSetoid_un_op IR.

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

End Appli1.

(** 
** Appli 2 : Prove that a function has no limit
*)

(**
1) sin(x)
We extract the 
*)



