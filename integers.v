(**
* Definitions
*)

(**
We extend the [nat] definition to include $$-\infty$$ : $$\overline{\mathbb{N}} = \mathbb{N} \cap \{-\infty\}$$
*)

Inductive nat_inf : Type :=
    | nat_finite : nat->nat_inf
    | nat_mInf : nat_inf.