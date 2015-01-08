(** Real sequences **)

Require Import Rbase.
Require Import Rfunctions.

Require Import CauchySeq.

Require Import Classical_Prop.

Require Import QArith.
Open Scope Q_scope.
Require Import CRtrans.

(**
* Definitions of the concepts on sequences
*)

Section Sequence_definitions.

Variable Un : nat->IR.

(**
** Sequence limits
*)

Section Sequence_Limits.

Open Local Scope Q_scope.

(** 
Definition of a sequence that converges to a real [l] :
$$\forall \epsilon > 0, \exists n_0 \in \mathbb{N}, \forall n \geq n_0, |u_n - l| < \epsilon$$
*)
Definition Un_convergent (l : IR) : Prop :=
    forall epsilon : IR, (epsilon [>] [0] -> exists n0 : nat, (forall n : nat, n >= n0 
        -> AbsSmall epsilon ((Un n) [-] l))).

(**
Definition of a sequence that diverges to $$+\infty$$ :
$$\forall A \in \mathbb{R}, \exists n_0 \in \mathbb{N}, \forall n \geq n_0, u_n \geq A$$
*)
Definition Un_divergent_pInf : Prop :=
   forall A : IR, (exists n0 : nat, forall n : nat, n >= n0 -> (Un n) [>=] A).

(**
Definition of a sequence that diverges to $$-\infty$$ :
$$\forall a \in \mathbb{R}, \exists n_0 \in \mathbb{N}, \forall n \geq n_0, u_n \leq a$$
*)
Definition Un_divergente_mInf : Prop :=
   forall a : IR, (exists n0 : nat, (forall n : nat, n >= n0 -> Un n [<=] a)).

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
$$(v_n)$$ is a subsequence if there exist a stricly increasing function 
$$\phi : \mathbb{N} \rightarrow \mathbb{N}$$
such that $$\forall n \in \mathbb{N}, v_n = u_{\phi(n)}$$
*)
Definition Un_subsequence (Vn : nat->IR) : Prop :=
    exists (phi : nat->nat), int_strict_increasing_func phi 
        -> (forall n : nat, (Vn n) [=] (Un (phi n))).

End SubSequence.


End Sequence_definitions.


