Require Export SAMPL.logic.

(**
* Definitions
*)

(**
** Real numbers form a ring : $$(\mathbb{R}, +, \cdot)$$
We use the axiomatic defintion of the real numbers in the standard library
*)

Require Export Rbase.
Open Scope R_scope.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.abstract_algebra.

Instance R_equiv: Equiv R := eq.
Instance R_plus: Plus R := Rplus.
Instance R_0: Zero R := R0.
Instance R_1: One R := R1.
Instance R_mult: Mult R := Rmult.
Instance R_negate: Negate R := Ropp.

Instance: Ring R.
Proof.
    (* Unfold the axioms of the algebraic structures *)
    repeat (split; try apply _); repeat intro.
    (* Now we prove these axioms : *)
        (* Associativity of addition *)
        assert (x + (y + z) = x + y + z) as H_assoc ; apply eq_sym ; apply Rplus_assoc ; apply H_assoc.
        (* Neutral element for the addition (left and right) *)
        apply Rplus_0_l. rewrite Rplus_comm ; apply Rplus_0_l.
        (* Neutral element for the opposite (left and right) *)
        rewrite Rplus_comm ; apply Rplus_opp_r. apply Rplus_opp_r.
        (* Commutativity of addition *)
        apply Rplus_comm.
        (* Associativity of multiplication *)
        assert (x * (y * z) = x * y * z) as H_assoc ; apply eq_sym ; apply Rmult_assoc ; apply H_assoc.
        (* Neutral element for the multiplication (left and right) *)
        apply Rmult_1_l. rewrite Rmult_comm ; apply Rmult_1_l.
        (* Commutativity of multiplication *)
        apply Rmult_comm.
        (* Distributivity of multiplication over addition *)
        apply Rmult_plus_distr_l.
Qed.

Instance R_le: Le R := Rle.
Instance R_lt: Lt R := Rlt.

(**
** $$\mathbb{R}$$ bounds
*)

(**
We here introduce the notion of infinity for the real numbers.
We simply define it as a predicate, to be able to deal with it as a "classical number"
(i.e. use the type [R])
/!\ The value [x] of these definitions should not be used /!\
*)

Definition pInfinite (x : R) : Prop := forall (y : R), (x > y)%R.
Definition mInfinite (x : R) : Prop := forall (y : R), (x < y)%R.
Definition real (x : R) : Prop :=  ~ (pInfinite x) /\ ~ (mInfinite x).

Axiom reals_infinity : forall (x : R), pInfinite x \/ mInfinite x \/ (~ (pInfinite x) /\ ~ (mInfinite x)).

(**
[R_inf] is a helper type. It is intended to be used in match constructions.
*)

Inductive R_inf (x:R) := 
    | pInf : pInfinite x -> R_inf x
    | mInf : mInfinite x -> R_inf x
    | xReal : real x -> R_inf x.

(**
Using example in a Definition :
 [Definition test (x : R) := 
    forall (inf_x : R_inf x),
      match inf_x with
        | pInf H_pInfinite =>  True
        | mInf H_mInfinite =>  True
        | xReal H_not_pInfinite H_not_mInfinite =>  True
      end. ]
*)

(**
** Subsets of $$\mathbb{R}$$
*)

(**
Chat TI-Planet
Channel: Language:
(10:13:38) Victor_D: salut choups
We define the usual predicate domains : $$\mathbb{R}^+$$, $$\mathbb{R}^-$$, $$\mathbb{R}^*$$.
*)

Definition R_positive (x : R) : Prop := x >= 0.
Definition R_negative (x : R) : Prop := x <= 0.
Definition R_non_zero (x : R) : Prop := ~ (x = 0).
