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

Variable Un : nat->R.

(**
** Sequence limits
*)

Section Sequence_Limits.

Open Local Scope Q_scope.

Definition Un_convergent (l : IR) : Prop :=
   forall epsilon : IR, (epsilon [>] ('1)%CR -> 
      (exists n0 : nat, (forall n : nat, n >= n0 -> (R_dist (Un n) l < epsilon)%R))).

Definition Un_divergent_pInf : Prop :=
   forall A : R, (exists n0 : nat, (forall n : nat, n >= n0 -> (Un n >= A)%R)).

Definition Un_divergente_mInf : Prop :=
   forall a : R, (exists n0 : nat, (forall n : nat, n >= n0 -> (Un n <= a)%R)).

End Sequence_Limits.

(**
** Sequence bounds
*)

Section Sequence_Bounds.

Definition Un_bounded : Prop := 
   exists M : R, (forall n : nat, (Rabs (Un n) < M)%R).

Definition Un_upperBound : Prop :=
   exists (M:R), (forall n : nat, (Un n <= M)%R).

Definition Un_lowerBound : Prop :=
   exists (m:R), (forall n : nat, (Un n <= m)%R).

End Sequence_Bounds.

(**
* Monotonicity of sequences
*)

Section Sequence_monotonicity.

Definition Un_increasing : Prop := 
   forall n : nat, (Un (S n) >= Un n)%R.

Definition Un_decreasing : Prop := 
   forall n : nat, (Un (S n) <= Un n)%R.

Definition Un_stationary : Prop :=
   exists n0 : nat, (forall n : nat, n >= n0 -> (Un (S n) = Un n)%R).

Definition Un_periodic : Prop :=
   exists T : nat, (forall n : nat, (Un (n + T) = Un n)%R).

Definition Un_constant : Prop :=
   forall n : nat, (Un (S n) = Un n)%R.

End Sequence_monotonicity.

(**
* Subsequences
*)

Section SubSequence.

Definition int_strict_increasing_func (f : nat->nat) : Prop :=
    forall n : nat, (f (S n)) > (f n).
Lemma int_strict_increasing_func_n : 
   forall (f : nat->nat), int_fonction_strict_croissante f -> forall n:nat, (f n) >= n.
Admitted.

Definition Un_subsequence (Vn : nat->R) : Prop :=
    exists (phi : nat->nat), int_fonction_strict_croissante phi -> (forall n : nat, ((Vn n) = (Un (phi n)))%R).

End SubSequence.


End Sequence_definitions.


