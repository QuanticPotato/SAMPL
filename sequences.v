Require Export SAMPL.reals.

(**
* Definitions of the concepts on sequences
*)

Section Sequence_definitions.

Variable Un : nat->IR.

(**
** Sequence limits
*)

Section Sequence_Limits.

(**
Definition of sequence limit :
- $$u_n$$ converges : $$\lim\limits_{n \to +\infty} u_n = l \in \mathbb{R}$$
- $$u_n$$ diverges to $$+\infty$$ : $$\lim\limits_{n \to +\infty} u_n = +\infty$$
- $$u_n$$ diverges to $$-\infty$$ : $$\lim\limits_{n \to +\infty} u_n = -\infty$$
*)

Inductive Un_limit : Type :=
    | Un_convergent : IR->Un_limit
    | Un_divergent_pInf : Un_limit
    | Un_divergent_mInf : Un_limit.

(**
For the three cases, we associate a predicate :
- $$u_n$$ converges : $$\forall \epsilon > 0, \exists n_0 \in \mathbb{N}, \forall n \geq n_0, |u_n - l| < \epsilon$$
- $$u_n$$ diverges to $$+\infty$$ : $$\forall A \in \mathbb{R}, \exists n_0 \in \mathbb{N}, \forall n \geq n_0, u_n \geq A$$
- $$u_n$$ diverges to $$-\infty$$ : $$\forall a \in \mathbb{R}, \exists n_0 \in \mathbb{N}, \forall n \geq n_0, u_n \leq a$$
*)

Definition Un_limitProp (L : Un_limit) : Prop :=
    match L with
        | Un_convergent l => forall epsilon : IR, (epsilon [>] [0] -> exists n0 : nat, (forall n : nat, n >= n0 
                -> AbsSmall epsilon ((Un n) [-] l)))
        | Un_divergent_pInf => forall A : IR, (exists n0 : nat, forall n : nat, n >= n0 -> (Un n) [>=] A)
        | Un_divergent_mInf => forall a : IR, (exists n0 : nat, (forall n : nat, n >= n0 -> Un n [<=] a))
    end.

(**
$$\lim\limits_{n \to +\infty} u_n \in \overline{\mathbb{R}}$$, so we define an helper 
to use the limit value ($$\in \overline{\mathbb{R}}$$) with the [IR_inf] type
*)

Definition Un_limit_value (L : Un_limit) : IR_inf :=
    match L with
        | Un_convergent l => real l
        | Un_divergent_pInf => pInf
        | Un_divergent_mInf => mInf
    end.

End Sequence_Limits.

(**
** Sequence bounds
*)

Section Sequence_Bounds.

(**
Definition of a bounded sequence :
$$\exists M \in \mathbb{R}, \forall n \in \mathbb{N}, |u_n| \leq M$$
*)
Definition Un_bounded : Prop := 
   exists M : IR, (forall n : nat, AbsSmall M (Un n)).

(** 
Definition of a sequence that has an upper-bound :
$$\exists M \in \mathbb{R}, \forall n \in \mathbb{N}, u_n \leq M$$
*)
Definition Un_upperBound : Prop :=
   exists (M : IR), (forall n : nat, Un n [<=] M).

(** 
Definition of a sequence that has an upper-bound :
$$\exists m \in \mathbb{R}, \forall n \in \mathbb{N}, u_n \leq m$$
*)
Definition Un_lowerBound : Prop :=
   exists (m:IR), (forall n : nat, Un n [<=] m).

End Sequence_Bounds.

(**
* Monotonicity of sequences
*)

Section Sequence_monotonicity.

(**
Definition of an increasing sequence : 
$$\forall n \in \mathbb{N}, u_{n+1} \geq u_n$$
*)
Definition Un_increasing : Prop := 
   forall n : nat, Un (S n) [>=] Un n.

(**
Definition of a decreasing sequence : 
$$\forall n \in \mathbb{N}, u_{n+1} \leq u_n$$
*)
Definition Un_decreasing : Prop := 
   forall n : nat, Un (S n) [<=] Un n.

(**
Definition of a stationary sequence :
$$\exists n_0 \in \mathbb{N}, \forall n \geq n_0, u_{n + 1} = u_n$$
*)
Definition Un_stationary : Prop :=
   exists n0 : nat, (forall n : nat, n >= n0 -> Un (S n) [=] Un n).

(**
Definition of a periodic sequence :
$$\exists T \in \mathbb{N}^*, \forall n \in \mathbb{N}, u_{n + T} = u_n$$
*)
Definition Un_periodic : Prop :=
   exists T : nat, (forall n : nat, Un (n + T) [=] Un n).

(**
Definition of a constant sequence :
$$\forall n \in \mathbb{N}, u_{n + 1} = u_n$$
*)
Definition Un_constant : Prop :=
   forall n : nat, Un (S n) [=] Un n.

End Sequence_monotonicity.

(**
* Subsequences
*)

Section SubSequence.

Definition int_strict_increasing_func (f : nat->nat) : Prop :=
    forall n : nat, (f (S n)) > (f n).
Lemma int_strict_increasing_func_n : 
   forall (f : nat->nat), int_strict_increasing_func f -> forall n:nat, (f n) >= n.
Admitted.

(** 
Definition of a subsequence : 
$$(v_n)$$ is a subsequence if there exist a stricly increasing function $$\phi : \mathbb{N} \rightarrow \mathbb{N}$$
such that $$\forall n \in \mathbb{N}, v_n = u_{\phi(n)}$$
*)
Definition Un_subsequence (Vn : nat->IR) : Prop :=
    exists (phi : nat->nat), int_strict_increasing_func phi -> (forall n : nat, (Vn n) [=] (Un (phi n))).

End SubSequence.


End Sequence_definitions.


