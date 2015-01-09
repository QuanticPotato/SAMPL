Require Export CoRN.reals.CauchySeq.

(**
* Definitions
*)

(**
We define a helper type for the limits : 
$$\overline{\mathbb{R}} = \mathbb{R} \cup \{+\infty\} \cup \{-\infty\}$$
*)

Inductive IR_inf : Type :=
    | real : IR -> IR_inf
    | pInf : IR_inf
    | mInf : IR_inf.

(**
** Absolute value
*)

(**
We use the CoRN definition, located in CoRN.algebra.COrdAbs.
*)

(** 
$$|a - b| \leq e \equiv$$ [AbsSmall e (a - b)] $$\equiv$$ [AbsSmall e (b - a)]
*)
