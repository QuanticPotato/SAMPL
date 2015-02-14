Require Import ZArith.

(**
* Maps as functions
(To avoid any confusions in this section, we call this maps "applications")
*)

(**
** Definition
We define partial functions with a Record structure : it allows to define a condition on the domain of definition.
We only deal with partial functions of the form : $$\in \mathcal{F}(I, \mathbb{E}), I \subset \mathbb{E}$$, where
$$\mathbb{E}$$ is a "super-set" (for example $$\mathbb{R}$ or $$\mathbb{Z}$$).
To build such a partial function (using [Build_PartFunct]), one needs (In this order) :
- A type [E], which  is the "super-set" $$\mathbb{E}$$
- A predicate [E -> Prop] that describes the domain of definition of the partial function.
- The function itself (The whole Record coerces to this type). It must includes the domain 
predicate (An example is given later in the file).
*)

Record PartFunct (E : Type) : Type := {
    pf_domain : E -> Prop ;
    pf_fun :> forall (x : E), pf_domain x -> E 
}.

(**
[Dom] allows to access the domain predicate of a PartFunct.
*)

Definition Dom := pf_domain.

(**
We extend the [PartFunct] definition for functions with two arguments.
Each argument has its own definition domain, and there is an extra predicate of the two variables together.
*)

Record PartFunct2 (E : Type) : Type := {
    pf2_dom1 : E -> Prop;
    pf2_dom2 : E -> Prop;
    pf2_cond : E -> E -> Prop;
    pf2_fun :> forall (x y : E), pf2_dom1 x -> pf2_dom2 y -> pf2_cond x y -> E
}.

(**
** Operations
*)

(**
The restriction of an application is the restriction of it's domain of definition
*)

Lemma cond_and (E : Type)(h1 h2 : E->Prop): forall x:E, (fun (x:E) => h1 x /\ h2 x) x -> h1 x.
Proof.
    intros ; destruct H ; assumption.
Qed.

Definition restriction (E : Type)(f : PartFunct E)(restr : E -> Prop) :=
    Build_PartFunct E (fun (x : E) => (Dom E f x) /\ restr x) 
    (fun (x:E)(H : (fun (x : E) => (Dom E f x) /\ restr x)  x) => f x (cond_and E (Dom E f) restr x H)).

(**
* Real functions
We here deal with partial functions $$I \rightarrow \mathbb{R}$$, where $$I$$ is a subset of $$\mathbb{R}.
(We also these functions in other chapters, unless otherwise stated)
We try as much as possible using the least hypothesis we can (e.g., only use COrdField for 
definitions/lemma that only require an order relation, instead of the full real structure.
*)

Require Export SAMPL.reals.
Open Scope R_scope.

Definition PartFunctR := PartFunct R. 

Section example_function.

(**
For example, let's build the function [ex_partFun] defined as follows : 
$$\left\{\begin{matrix}
\mathbb{R}^+ & \rightarrow  & \mathbb{R} \\
x  & \mapsto & e^x
\end{matrix}\right.$$
*)

Require Import Rtrigo_def.  (* Definition of exp *)

Definition ex_fun := fun (x : R)(_ : R_non_zero x) => exp x.

Definition ex_partFun_1 :=  Build_PartFunct R R_non_zero ex_fun.

(**
We can now use this definition as a classical function (We need to give a proof that the argument belongs
to the domain :
*)

Variable x:R.
Hypothesis Hx: R_non_zero x.
Let value := ex_partFun_1 x Hx.

End example_function.

Section function_properties.

(**
** Real functions properties
In this section, [f] is a partial function $$I \rightarrow \mathbb{R}$$.
*)

Variable f : PartFunctR.
Let I := Dom R f.

(**
We define the monotonicity of [f] as follows : 
- Increasing : $$\forall x, y \in I, x<y \Rigtharrow f(x) \leq f(y)$$ 
- Strictly increasing : $$\forall x, y \in I, x<y \Rigtharrow f(x) < f(y)$$ 
- Decreasing : $$\forall x, y \in I, x<y \Rigtharrow f(x) \geq f(y)$$ 
- Strictly decreasing : $$\forall x, y \in I, x<y \Rigtharrow f(x) > f(y)$$
- Constant : $$\forall x, y \in I, f(x) = f(y)$$
- Periodic (of period [T]) : $$\forall x \in \mathbb{I}, \forall k \in \mathbb{Z}, x+kT \in I \Rightarrow f(x+kT) = f(x)
*)

Definition increasing_fun := forall (x y : R)(Hx : I x)(Hy : I y),  x<y -> f x Hx <= f y Hy.
Definition strict_increasing_fun := forall (x y : R)(Hx : I x)(Hy : I y),  x<y -> f x Hx < f y Hy.
Definition decreasing_fun := forall (x y : R)(Hx : I x)(Hy : I y),  x<y -> f x Hx >= f y Hy.
Definition strict_decreasing_fun := forall (x y : R)(Hx : I x)(Hy : I y),  x<y -> f x Hx < f y Hy.
Definition constant_fun := forall (x y : R)(Hx : I x)(Hy : I y), f x Hx = f y Hy.
(*Definition periodic_fun (T : IR) := forall (x : R)(Hx : I x)(k : Z)(HT : I (x[+] (zring k)[*]T)), f x Hx [=] f (x[+] (zring k)[*]T) HT.*)

End function_properties.
