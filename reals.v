(***********************************************************************
*  ____   __   _  _  ____  __    *     Still Another Math library !    *
* / ___) / _\ ( \/ )(  _ \(  )   *-------------------------------------*
* \___ \/    \/ \/ \ ) __// (_/\ *        (c) Chauvin Barnabé          *
* (____/\_/\_/\_)(_/(__)  \____/ *  This file is distributed under the *
*                                *  terms of the GPL License Version 2 *
***********************************************************************)

Require Export structures.

(**
* Definitions
*)

Require Export Rbase.
Require Export Fourier.
Require Export Rbasic_fun.
Open Scope R_scope.

(**
** Real numbers form a ring : $$(\mathbb{R}, +, \cdot)$$
We use the axiomatic defintion of the real numbers in the standard library
*)

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
** Division
We extend the division definition available in the standard library to include the proof that 
the divisor is not 0.
For this, we first redefine the inverse of a real number.
*)

Definition RInv (x:R)(Hx : x<>0): R.
Admitted.

(**
If our construction is defined (i.e. the denominator is not zero), then it implies the Coq definition :
*)

Axiom RInv_Rinv : forall (x:R)(H : x<>0), RInv x H = Rinv x.

Definition RDiv (r1 r2:R)(H : r2<>0)  : R := r1 * (RInv r2 H).

Notation "x / y // Hy" := (RDiv x y Hy) (at level 0, y at next level).

(**
We prove the "obvious" lemmas for classic numbers : (like [R1_neq_R0])
*)

Lemma R2_neq_R0 : 2 <> 0. 
Proof.
    assert (2 > 0) by fourier ; apply Rgt_not_eq in H ; assumption.
Qed.
Hint Resolve R2_neq_R0: real.

Lemma R3_neq_R0 : 3 <> 0. 
Proof.
    assert (3 > 0) by fourier ; apply Rgt_not_eq in H ; assumption.
Qed.
Hint Resolve R3_neq_R0: real.

(**
We define the axiom of trichotomy.
We then define the tactic [trichotomy_cases] that generates the 3 differents cases (as 3 subgoals)
of this axiom for two real numbers.
We also define the tactic [different_cases] that is a subcase of the later. It applies for an hypothesis
[H : x <> y] (where [x] and [y] are real numbers) : it generates the 2 cases $$x < y$$ and $$x > y$$.
*)

Axiom trichotomy : forall (x y:R), x<y \/ x=y \/ x>y.

Ltac trichotomy_cases var ref := 
    let H := fresh in
        assert (var < ref \/ var = ref \/ var > ref) by (apply trichotomy) ; 
        destruct H ; [idtac | destruct H].

Ltac different_cases H :=
    match type of H with
        | ~ (?x [=] ?y) => trichotomy_cases x y ; [idtac | contradiction | idtac] ; clear H
        | _ => fail
    end.

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

(**
[R_inf] is a helper type. It is intended to be used in match constructions.
Using example in a Definition :
 [Definition test (x : R) := 
    forall (inf_x : R_inf x),
      match inf_x with
        | pInf H_pInfinite =>  True
        | mInf H_mInfinite =>  True
        | xReal H_not_pInfinite H_not_mInfinite =>  True
      end. ]
*)

Inductive R_inf (x:R) := 
    | pInf : pInfinite x -> R_inf x
    | mInf : mInfinite x -> R_inf x
    | xReal : real x -> R_inf x.

Axiom reals_infinity : forall (x : R), pInfinite x \/ mInfinite x \/ real x.

(**
In a proof, it might be useful to deal with the 3 different cases for a real number [x] : 
$$x \in \mathbb{R}$$, $$x = +\infty$$ or $$x = -\infty$$.
The tactic [inf_cases] introduces these cases :
*)

Ltac inf_cases var :=
    let H := fresh in
        match type of var with
            | R => assert ( pInfinite var \/ mInfinite var \/ real var) by (apply reals_infinity) ;
                destruct H ; [idtac | destruct H]
            | _ => idtac "The variable must be a real number (of type R)" ; fail
        end.

(**
** Subsets of $$\mathbb{R}$$
We define the usual predicate domains : $$\mathbb{R}^+$$, $$\mathbb{R}^-$$, $$\mathbb{R}^*$$.
*)

Definition R_positive (x : R) : Prop := x >= 0.
Definition R_negative (x : R) : Prop := x <= 0.
Definition R_non_zero (x : R) : Prop := ~ (x = 0).

(**
* Theorems and lemmas
*)

(**
We also (re)define basic theorems about the real numbers division. 
(Some are available in the standard library)
*)

Open Scope R_scope.

Lemma RInv_1 : RInv 1 R1_neq_R0 = 1.
Proof.
    rewrite RInv_Rinv. apply Rinv_1.
Qed.
Hint Resolve RInv_1: real.

Lemma RInv_r : forall (r:R)(H : r<>0), r * (RInv r H) = 1.
    intros ; rewrite RInv_Rinv ; now apply Rinv_r.
Qed.
Hint Resolve RInv_r: real.

Lemma RInv_0_lt_compat : forall (r:R)(H:r<>0), r>0 -> RInv r H > 0.
Proof.
    intros. rewrite RInv_Rinv.
    apply Rnot_le_lt ; red ; intros.
    absurd (1 <= 0) ; auto with real.
    replace 1 with (r * Rinv r) ; auto with real.
    replace 0 with (r * 0) ; auto with real.
Qed.
Hint Resolve RInv_0_lt_compat: real.

Lemma RDiv_pos_pos : forall (r1 r2:R)(H : r2 <> 0), r1 > 0 -> r2 > 0 -> r1 / r2 // H > 0.
Proof.
    intros. unfold RDiv. apply Rmult_gt_0_compat ; auto. now apply RInv_0_lt_compat.
Qed.
Hint Resolve RDiv_pos_pos: real.

Lemma Rdouble_var : forall (r:R)(Hr : r<>0), r = (r/2//R2_neq_R0) + (r/2//R2_neq_R0).
Proof.
    intros ; rewrite <- double ; unfold RDiv ; rewrite RInv_Rinv. rewrite <- Rmult_assoc.
    symmetry ; apply Rinv_r_simpl_m ; auto with real.
Qed.

Lemma RDiv_2_lt : forall (r:R), r > 0 -> r / 2 // R2_neq_R0 < r.
Proof.
    intros. pattern r at 2. rewrite Rdouble_var ;[idtac | now apply Rgt_not_eq].
    pattern (r) / (2) // (R2_neq_R0) at 1 ; rewrite <- Rplus_0_r ; apply Rplus_lt_compat_l.
    apply RDiv_pos_pos ; [auto | fourier].
Qed.

Lemma RDiv_simpl : forall (r1 r2 : R)(H : r2 <> 0), r2 * (r1 / r2 // H) = r1.
intros.
    unfold RDiv ; rewrite RInv_Rinv. 
    rewrite <- Rmult_assoc. rewrite (Rinv_r_simpl_m _ _ H). reflexivity.
Qed.

(**
Equalities
*)

Lemma Rminus_eq_compat_l : forall r r1 r2, r1 = r2 -> r - r1 = r - r2.
Proof.
    intros. apply Ropp_eq_compat in H. apply Rplus_eq_compat_l with (r:=r) in H. assumption.
Qed.

(**
** Inequalities
*)

Lemma Rlt_rewrite_le_l : forall (r1 r2 r3 r4 : R), r2 < r4 -> r1 <= r2 + r3 -> r1 < r4 + r3.
Proof.
     intros. assert ((r2 + r3) < (r4 + r3)). now apply Rplus_lt_compat_r. 
     (* Transitivity of the relation <= *)
     apply Rle_lt_trans with (r2 := r2 + r3) ; auto.
Qed.

Lemma Rlt_rewrite_le_r : forall (r1 r2 r3 r4 : R), r3 < r4 -> r1 <= r2 + r3 -> r1 < r2 + r4.
Proof.
    intros. rewrite Rplus_comm in H0. 
    apply  Rlt_rewrite_le_l with (r4:=r4) in H0 ; [rewrite Rplus_comm | idtac] ; auto.
Qed. 

Lemma Rlt_rewrite_lt_r : forall (r1 r2 r3 r4 : R), r3 < r4 -> r1 < r2 + r3 -> r1 < r2 + r4.
Proof.
    intros. assert ((r2 + r3) < (r2 + r4)). now apply Rplus_lt_compat_l.
     apply Rlt_trans with (r2 := r2 + r3) ; auto.
Qed.
