Require Import ZArith.
Open Scope Z_scope.
Require Import BinInt.
Require Import BinIntDef.
Require Import Psatz.

Section Arithmetique.

(* 0) Quelques petits trucs utils dans Z
   -------------------------------------  *)

(* TODO : Déplacer dans un chapitre approprié ! *)

(* Une tactique qui sert dans plusieures preuves : Disjonction de cas sur un entier relatif z.
   La tactique génère deux sous-buts : Si z=x et si z<>x  (x: argument de la tactique) )   *)
(* Arguments :  @z : variable
                @x : valeur de la disjonction *)
Ltac Zcases_on_value z x :=
    match goal with 
        (* etape 2) *) | [ Hcases_on_value : {z = x} + {z <> x} |- _ ] => destruct Hcases_on_value
                          (* On détruit la somme disjointe pour obtenir deux sous-buts *)
        (* etape 1) *) | _ => cut ({z = x} + {z <> x}) ;
                            [intro Hcases_on_value | (exact (Z.eq_dec z x))] ;
                            Zcases_on_value z x
                            (* Le premier sous-but est celui qui nous interesse : on effectue un simple intro.
                            Le deuxieme est trivial a prouver *)
    end.

Lemma Zmult_1 : forall (x y : Z), x * y = 1 -> ((x = 1) /\ (y = 1)) \/ ((x = -1) /\ (y = -1)).
Proof.
    intros. Zcases_on_value x 1.
    (* Si x=1 *) left. rewrite e in H. assert (y = 1). rewrite Z.mul_1_l in H. assumption. split ; assumption ; assumption.
    (* Si x=-1 *) Zcases_on_value x (-1). right. rewrite e in H. assert (y = -1).
Search ( _ * _ = _ * _ ).
        (* $-1 * y = 1 \Leftrightarrow y = -1$*)
            assert (-1 * (-1 * y) = -1 * 1). rewrite H ; easy. 
            assert (-1 * (-1 * y) = y) by ring ; rewrite -> H1 in H0.
            assert (-1 * 1 = -1) by ring ; rewrite -> H2 in H0.
            assumption.
        split ; assumption ; assumption.
    (* Si $x \not\in \{1, -1\}$, On montre la contradiction dans les hypothèses *)
        assert (y >= 0 \/ y <= 0) by lia.
        nia.
Qed.

(* 1) Divisibilité, congruence
   ---------------------------  *)

Definition divide (a b : Z) : Prop := exists (k : Z), b = k*a.
Notation "( x | y )" := (divide x y) (at level 0).

(* Les signes ne changent pas la divisibilité de deux nombres. *)
Lemma divisibilite_signe : forall (a b :Z), (a | b) <-> ((-a) | b).
intros. unfold iff. split.
(* Pour les deux implications, on utilise la définition de la divisibilité. *)
(* Première implication : *) unfold divide ; intro H ; destruct H ; exists (-x) ; rewrite H ; ring.
(* Deuxième implication : *) unfold divide ; intro H ; destruct H ; exists (-x) ; rewrite H ; ring.
Qed.
(* On a aussi bien entendu le lemme [divide a b <-> divide a (-b)] *)

(* La relation de divisibilité est antisymétrique 
   (Elle est vraiment antisymétrique dans N. Dans Z, on a $a=b$ ou $a=-b$ *)
Lemma divisibilite_antisym : forall (a b : Z), (a | b) -> (b | a) -> a = b \/ a = -b.
intros a b H1 H2.
destruct H1 ; destruct H2 ; rewrite H in H0 ; Zcases_on_value a 0.
(* Si a=0 : *) left ; rewrite H ; rewrite e ; ring.
(* Si a<>0 : *) 
    (* On factorise [a = x0 * (x * a)] par a *)
        apply Zplus_eq_compat with (p := -a)(q:=-a) in H0. 
        rewrite Zegal_left in H0. assert (a*((x0 * x) - 1) = 0) as H1.
        rewrite -> H0. ring.
    (* On a donc $x, x0 \in \{-1, 1} *)
        apply Zmult_integral in H1.
        destruct H1. contradiction.
        apply Zplus_eq_compat with (p := 1)(q:=1) in H1. 
            simpl in H1.
            assert (x0 * x - 1 + 1 = x0 * x) as H2 by ring.
            rewrite -> H2 in H1.
        apply Zmult_1 in H1. elim H1 ; intro H3 ; elim H3 ; intros.
        (* Si x = 1 et x0 = 1*)
            left. rewrite H. rewrite H5. ring.
        (* Si x = -1 et x0 = -1 *)
            right. rewrite H. rewrite H5. ring.
    (* Il ne reste plus que les preuves 1=1, a=a ... dûes aux assertions *)
        reflexivity. reflexivity. reflexivity.
Qed.


