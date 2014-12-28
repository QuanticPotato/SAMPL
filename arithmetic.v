Require Import ZArith.
Open Scope Z_scope.
Require Import BinInt.
Require Import BinIntDef.
Require Import Psatz.

Section Arithmetique.

(* 0) A few things useful in Z
   -------------------------------------  *)

(* TODO : Move into an appropriate chapter ! *)

(* This tactic generates two goals, depending on the value of x (equal or different)  *)
(* Usage :  @z : variable
            @x : value for the disjunction *)
Ltac Zcases_on_value z x :=
    match goal with 
        (* step 2) *) | [ Hcases_on_value : {z = x} + {z <> x} |- _ ] => destruct Hcases_on_value
                          (* Obtain the two sub-goals *)
        (* step 1) *) | _ => cut ({z = x} + {z <> x}) ;
                            [intro Hcases_on_value | (exact (Z.eq_dec z x))] ;
                            Zcases_on_value z x
                            (* The first goal is the one we want, and the second one is trivial. *)
    end.

Lemma Zmult_1 : forall (x y : Z), x * y = 1 -> ((x = 1) /\ (y = 1)) \/ ((x = -1) /\ (y = -1)).
Proof.
    intros. Zcases_on_value x 1.
    (* If x=1 *) left. rewrite e in H. assert (y = 1). rewrite Z.mul_1_l in H. assumption. split ; assumption ; assumption.
    (* If x=-1 *) Zcases_on_value x (-1). right. rewrite e in H. assert (y = -1).
Search ( _ * _ = _ * _ ).
        (* $-1 * y = 1 \Leftrightarrow y = -1$*)
            assert (-1 * (-1 * y) = -1 * 1). rewrite H ; easy. 
            assert (-1 * (-1 * y) = y) by ring ; rewrite -> H1 in H0.
            assert (-1 * 1 = -1) by ring ; rewrite -> H2 in H0.
            assumption.
        split ; assumption ; assumption.
    (* If (x,y)<>(1,1) and (x,y)<>(-1,-1), Show the contradiction in the hypothesis  *)
        assert (y >= 0 \/ y <= 0) by lia.
        nia.
Qed.

(* 1) Divisibility, congruence
   ---------------------------  *)

(* Definition from the stdlib *)
Definition divide (a b : Z) : Prop := exists (k : Z), b = k*a.
Notation "( x | y )" := (divide x y) (at level 0).

(* Signs don't change the divisibility *)
Lemma divisibilite_signe : forall (a b :Z), (a | b) <-> ((-a) | b).
intros. unfold iff. split.
(* Use the definition of the divisibility *)
(* First implication : *) unfold divide ; intro H ; destruct H ; exists (-x) ; rewrite H ; ring.
(* Second implication : *) unfold divide ; intro H ; destruct H ; exists (-x) ; rewrite H ; ring.
Qed.

(* The divisibility relation is (almost) antisymetric in Z. 
   (It is really antisymetric in N) *)
Lemma divisibilite_antisym : forall (a b : Z), (a | b) -> (b | a) -> a = b \/ a = -b.
intros a b H1 H2.
destruct H1 ; destruct H2 ; rewrite H in H0 ; Zcases_on_value a 0.
(* If a=0 : *) left ; rewrite H ; rewrite e ; ring.
(* If a<>0 : *) 
    (* Factorize [a = x0 * (x * a)] b a *)
        apply Zplus_eq_compat with (p := -a)(q:=-a) in H0. 
        rewrite Zegal_left in H0. assert (a*((x0 * x) - 1) = 0) as H1.
        rewrite -> H0. ring.
    (* Now we have $x, x0 \in \{-1, 1} *)
        apply Zmult_integral in H1.
        destruct H1. contradiction.
        apply Zplus_eq_compat with (p := 1)(q:=1) in H1. 
            simpl in H1.
            assert (x0 * x - 1 + 1 = x0 * x) as H2 by ring.
            rewrite -> H2 in H1.
        apply Zmult_1 in H1. elim H1 ; intro H3 ; elim H3 ; intros.
        (* If x = 1 and x0 = 1*)
            left. rewrite H. rewrite H5. ring.
        (* If x = -1 and x0 = -1 *)
            right. rewrite H. rewrite H5. ring.
    (* It remains trivial goals 1=1, a=a ... because of the assertions *)
        reflexivity. reflexivity. reflexivity.
Qed.


