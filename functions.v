Require Import ZArith.

Section Functions_definitions.

(**
* Real functions
We here deal with partial functions $$I \rightarrow \mathbb{R}$$, where $$I$$ is a subset of $$\mathbb{R}.
(We also these functions in other chapters, unless otherwise stated)
We try as much as possible using the least hypothesis we can (e.g., only use COrdField for 
definitions/lemma that only require an order relation, instead of the full real structure.
*)

Require Import CoRN.algebra.CSetoidFun.
Require Import CoRN.reals.CauchySeq.

(**
All of our functions will be satisfy these properties (They are defined in the CoRN lib, and the later
flows naturally from the first) :
- Strong functional extensionality : $$\forall x_1, ..., x_n, y_1, ..., y_n, f(\rightarrow{x}) \neq f(\rightarrow{y}) 
\Rightarrow (x_1 \neq y_1 \/ ... \/ x_n \neq y_n)$$ 
- Functional extensionality : If two functions, given the same input, produce the same value, then they are equal.
*)

(**
We use the CoRN definiton of partial function : [PartFunct] (Defined in CoRN.algebra.CSetoidFun)
To build such a partial function (using [Build_PartFunct]), one needs (In this order) :
- A CSetoid [S], which is the root carrier of the domain of definition, and the codomain : 
$$f : D_f \rightarrow S$$, with $$D_f \subset S$$.
- A predicate [S -> CProp] that characterize the domain of the partial function.
- A proof that this predicate is well-defined (i.e. $$\forall x, y \in S, P(x) \land x=y \Rightarrow P(y)$$)
- The function itself (The whole Record coerce to this type). It has to be defined in a special way (To include
the domain predicate) : [(fun x P => )].
- A proof that the function has strong functional extensionality

The definition PartIR wrap for every real functions.
*)

Section domain_predicates.

(**
We define the usual predicate domains : $$\mathbb{R}^+$$, $$\mathbb{R}^-$$, $$\mathbb{R}^*$$,
and their respective well-definedness proofs.
*)

(*Definition IR_positive (x : R) : CProp := {Hx : R->CProp | x [>=] [0]}.*)
Definition IR_positive (x : IR) : CProp := x [>=] [0].
Definition IR_negative (x : IR) : CProp := x [<=] [0].
Definition IR_non_zero (x : IR) : CProp := x [#] [0].

Lemma IR_positive_wd : pred_wd IR IR_positive.
Proof.
    (* Simplify the goal *)
    red ; unfold IR_positive ; intros.
    (* Rewrite [y] to [x] in the goal (Need extra steps to use csetoid_rewrite) *)
    rewrite -> grEq_def ; rewrite -> leEq_def ; apply eq_symmetric in H0 ; csetoid_rewrite H0 ; rewrite <- leEq_def ; rewrite <- grEq_def.
    assumption.
Qed.

Lemma IR_negative_wd : pred_wd IR IR_negative.
Proof.
    (* Simplify the goal *)
    red ; unfold IR_negative ; intros.
    (* Rewrite [y] to [x] in the goal (Need extra steps to use csetoid_rewrite)  *)
    rewrite -> leEq_def ; apply eq_symmetric in H0 ; csetoid_rewrite H0 ; rewrite <- leEq_def.
    assumption.
Qed.

Lemma IR_non_zero_wd : pred_wd IR IR_non_zero.
Proof.
    (* Simplify the goal *)
    red ; unfold IR_non_zero ; intros.
    (* Rewrite [y] to [x] in the goal *)
    apply eq_symmetric in H ; csetoid_rewrite H.
    assumption.
Qed.

End domain_predicates.

Section example_function.

Section PartFunct2.

(**
In this section, we extend thee [PartFunct] definitions for functions with two arguments.
Each argument has its own definition domain, and there is an extra predicate of the two variables together.
[S1] and [S2] are the domain of the two variables. [S3] is the codomain.
*)

Record PartFunct2 (S1 S2 S3 : CSetoid) : Type := {
    pf2_dom1 : S1 -> CProp;
    pf2_dom2 : S2 -> CProp;
    pf2_fun :> forall (x:S1)(y:S2), pf2_dom1 x -> pf2_dom2 y -> S3;
    pf2_strext : forall (x x':S1)(y y':S2) (Hx:pf2_dom1 x)(Hx':pf2_dom1 x') (Hy:pf2_dom2 y)(Hy':pf2_dom2 y'),
        (pf2_fun x y Hx Hy) [#] (pf2_fun x' y' Hx' Hy') -> x[#]x' or y[#]y'
}.

End PartFunct2.

(**
For example, let's build the function [ex_partFun] defined as follows : 
\left\{\begin{matrix}
\mathbb{R}^+ & \rightarrow  & \mathbb{R} \\
x  & \mapsto & \sin(x)
\end{matrix}\right.$$
*)

Require Import CoRN.transc.PowerSeries.

Variable S : Type.

Definition ex_fun := fun (x : IR)(_ : IR_non_zero x) => Sin x.

Lemma ex_fun_strext : forall (x y : IR) (Hx : IR_non_zero x) (Hy : IR_non_zero y),
    ex_fun x Hx [#] ex_fun y Hy -> x [#] y.
Proof.
Admitted.

Definition ex_partFun_1 :=  Build_PartFunct IR IR_non_zero IR_non_zero_wd
    ex_fun ex_fun_strext.

(**
We can now use this definition as a classical function (We need to give a proof that the argument belongs
to the domain :
*)

Variable x:IR.
Hypothesis Hx: IR_non_zero x.
Let value := ex_partFun_1 x Hx.

End example_function.

Section function_properties.

Open Local Scope Z_scope.

(**
** Real functions properties
In this section, [f] is a partial function $$I \rightarrow \mathbb{R}$$.
*)

Variable f:PartIR.
Let I := Dom f.

(**
We define the monotonicity of [f] as follows : 
- Increasing : $$\forall x, y \in I, x<y \Rigtharrow f(x) \leq f(y)$$ 
- Strictly increasing : $$\forall x, y \in I, x<y \Rigtharrow f(x) < f(y)$$ 
- Decreasing : $$\forall x, y \in I, x<y \Rigtharrow f(x) \geq f(y)$$ 
- Strictly decreasing : $$\forall x, y \in I, x<y \Rigtharrow f(x) > f(y)$$
- Constant : $$\forall x, y \in I, f(x) = f(y)$$
- Periodic (of period [T]) : $$\forall x \in \mathbb{I}, \forall k \in \mathbb{Z}, x+kT \in I \Rightarrow f(x+kT) = f(x)
*)

Definition increasing_fun := forall (x y : IR)(Hx : I x)(Hy : I y),  x[<]y -> f x Hx [<=] f y Hy.
Definition strict_increasing_fun := forall (x y : IR)(Hx : I x)(Hy : I y),  x[<]y -> f x Hx [<] f y Hy.
Definition decreasing_fun := forall (x y : IR)(Hx : I x)(Hy : I y),  x[<]y -> f x Hx [>=] f y Hy.
Definition strict_decreasing_fun := forall (x y : IR)(Hx : I x)(Hy : I y),  x[<]y -> f x Hx [<] f y Hy.
Definition constant_fun := forall (x y : IR)(Hx : I x)(Hy : I y), f x Hx [=] f y Hy.
Definition periodic_fun (T : IR) := forall (x : IR)(Hx : I x)(k : Z)(HT : I (x[+] (zring k)[*]T)), f x Hx [=] f (x[+] (zring k)[*]T) HT.

End function_properties.

End Functions_definitions.

