Require Import CoRN.algebra.CSetoids.
Require Import CoRN.reals.CauchySeq.
Require Import CoRN.ftc.MoreIntervals.

Require Import SAMPL.reals.
Require Import SAMPL.functions.

(**
* Definitions
*)

Section Differentiability_definitions.

(**
** Differentiability
*)

(**
In this part, [I] is an interval $$\neq \emptyset$$ of $$\mathbb{R}, $$f : I \rightarrow \mathbb{R}$$.
It's likely some of the definitions below already exist in the CoRN library (because we are using CoRN's [PartFunc]
definition for partial functions. If it is the case, we prove the equivalence between our definitions and the
CoRN's ones.
*)

Variable f : PartIR.
Let I := Dom f.
Section difference_quotient.

(**
We define the difference quotient of [f] as follows :
$$\Delta_f (x_0, x) = \frac{f(x) - f(x_0)}{x - x_0}$$
(N.B. : (\Delta_f (x_0, x) = \Delta_f (x, x_0)$$)
*)

Variable x0 : IR.
Hypothesis H_x0 : I x0.
Variable x : IR.
Hypothesis H_x_I : I x.
Hypothesis H_x_not_x0 : x[#]x0.

Lemma x_x0_not_zero : x[-]x0 [#] [0].
Proof. 
    apply minus_ap_zero ; assumption.
Admitted.

Definition diff_quotient :=  (f x H_x_I [-] f x0 H_x0) [/] (x[-]x0) [//] x_x0_not_zero.

End difference_quotient.

Check diff_quotient.

Lemma dq_pos_increasing_fun : (increasing_fun f) <-> (forall (x x0 : IR)(Hx : I x)(Hx0 : I x0), I x 
     -> I x0 -> (diff_quotient x0 Hx0 x Hx) [>=] [0]).
Proof.
    unfold iff ; split.
        intros. 

End Differentiability_definitions.


