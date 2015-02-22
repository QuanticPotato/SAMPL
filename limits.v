Require Import ZArith.

Require Export SAMPL.functions.
Open Scope R_scope.


(**
* Definitions
*)

Section adherent_point_def.

(**
An adherent point [a] (also called closure point or contact point) of a subset [I] is such that :
$$\forall \epsilon > 0, ]a - \epsilon, a + \epsilon[ \cap I \neq \emptyset$$.
For the reals $$\mathbb{R}$$, [a] is adherent to a subset $$I \subset \mathbb{R}$$ if and
only if $$a \in I$$ or $$a$$ is a bound of $$I$$.
*)

Definition adherent_point (a : R)(I : R->Prop) :=  forall (e:R), e>0 -> exists (x:R), I x /\ Rabs (x - a) < e.

Variable I : R -> Prop.

(**
If a point belongs to [I], then this point is adherent to [I].
*)

Lemma adherent_point_in (a : R) : I a -> adherent_point a I.
Proof.
    intro H. unfold adherent_point. intros. exists a. split ; auto.
    replace (a - a) with 0. now rewrite Rabs_R0. ring.
Qed.

End adherent_point_def.

Section Limit_definitions.

(**
** Predicate true at the neighbourhood of $$x_0$$
The predicate [P x] (defined on $$I \subset \mathbb{R}$$) is true at the neighbourhood of 
$$x_0 \in \overline{\mathbb{R}}$$ if : 
- $$x_0$$ is finite : $$\exists \delta > 0, \forall x \in \[x_0 - \delta, x_0 + \delta \] \cap I, P(x) \quad \mathrm{true}$$
- $$x_0 = +\infty$$ : $$\exists a \in \mathbb{R}, \forall x \in \[a, +\infty \[ \cap I, P(x) \quad \mathrm{true}$$
- $$x_0 = -\infty$$ : $$\exists a \in \mathbb{R}, \forall x \in \]-\infty, a\] \cap I, P(x) \quad \mathrm{true}$$
*)

Section neighbourhood_def.

Variable I : R -> Prop.

Definition predicate_neighbourhood (P : (forall x : R, I x -> Prop)) (x0 : R) : Prop :=
    forall (x0_inf : R_inf x0),
    match x0_inf with
        | xReal H => exists (d:R), d > 0 /\ forall (x : R)(Hx : I x), Rabs (x - x0) < d -> P x Hx
        | pInf H => exists (a:R), forall (x : R)(Hx : I x), x >= a -> P x Hx
        | mInf H => exists (a:R), forall (x : R)(Hx : I x), x <= a -> P x Hx
end.

End neighbourhood_def.

(**
** Limits of real functions
*)

Section limit_def.

Variable f : PartFunct R.
Let I := Dom R f.

(**
We define the limit [l] of the function [f x] as [x] approaches [x0] with 
9 different cases (depending on [l] and [x0]), and we assign a predicate to each case :
- [x0] is finite :
  - [l] is finite : $$x_0 \in \mathbb{R}, \lim\limits_{x \to x_0} f(x) = l \in \mathbb{R}$$ :
$$\forall \epsilon>0, \exists \delta>0, \forall x \in \[x_0 - \delta, x_0 + \delta\] \cap I, |f(x)-l| \leq \epsilon$$
  - [l] is $$+\infty$$ : $$x_0 \in \mathbb{R}, \lim\limits_{x \to x_0} f(x) = +\infty$$ :
$$\forall A \in \mathbb{R}, \exists \delta>0, \forall x \in \[x_0 - \delta, x_0 + \delta\] \cap I, f(x) \geq A$$
  - [l] is $$-\infty$$ : $$x_0 \in \mathbb{R}, \lim\limits_{x \to x_0} f(x) = -\infty$$ :
$$\forall A \in \mathbb{R}, \exists \delta>0, \forall x \in \[x_0 - \delta, x_0 + \delta\] \cap I, f(x) \leq A$$
- [x0] is $$+\infty$$ :
  - [l] is finite : $$\lim\limits_{x \to +\infty} f(x) = l \in \mathbb{R}$$ :
$$\forall \epsilon>0, \exists a \in \mathbb{R}, \forall x \in I, x \geq a \Rightarrow |f(x)-l| \leq \epsilon$$
  - [l] is $$+\infty$$ : $$\lim\limits_{x \to +\infty} f(x) = +\infty$$ :
$$\forall A \in \mathbb{R}, \exists a \in \mathbb{R}, \forall x \in I, x \geq a \Rightarrow f(x) \geq A$$
  - [l] is $$-\infty$$ : $$\lim\limits_{x \to +\infty} f(x) = -\infty$$ :
$$\forall A \in \mathbb{R}, \exists a \in \mathbb{R}, \forall x \in I, x \geq a \Rightarrow f(x) \leq A$$
- [x0] is $$-\infty$$ :
  - [l] is finite : $$\lim\limits_{x \to -\infty} f(x) = l \in \mathbb{R}$$ :
$$\forall \epsilon>0, \exists a \in \mathbb{R}, \forall x \in I, x \leq a \Rightarrow |f(x)-l| \leq \epsilon$$
  - [l] is $$+\infty$$ : $$\lim\limits_{x \to -\infty} f(x) = +\infty$$ :
$$\forall A \in \mathbb{R}, \exists a \in \mathbb{R}, \forall x \in I, x \leq a \Rightarrow f(x) \geq A$$
  - [l] is $$-\infty$$ : $$\lim\limits_{x \to -\infty} f(x) = -\infty$$ :
$$\forall A \in \mathbb{R}, \exists a \in \mathbb{R}, \forall x \in I, x \leq a \Rightarrow f(x) \leq A$$
(We use [predicate_neighbourhood] to match [x0]).
*)

Definition limit (x0 l : R) : Prop :=
    forall (l_inf : R_inf l),
    match l_inf with
        | xReal H => forall (e : R), e > 0 ->predicate_neighbourhood I (fun (x:R)(Hx: Dom R f x) => Rabs ((f x Hx) - l) < e) x0
        | pInf H => forall (A : R),predicate_neighbourhood I (fun (x:R)(Hx: Dom R f x) =>  (f x Hx) >= A) x0
        | mInf H => forall (A : R),predicate_neighbourhood I (fun (x:R)(Hx: Dom R f x) => (f x Hx) <= A) x0
    end.

Definition limitExists (x0 : R) : Prop := exists (l : R), limit x0 l.

End limit_def.

(**
We also define one-sided limits (When x_0 \in \mathbb{R}) : 
- When $x$ approach $x_0$ from above (right) :
$\lim\limits_{x \to x_0^+} f(x) = \left. \lim\limits_{x_0} f \right|_{I \cap ] x_0, +\infty[} = l$
- When $x$ approach $x_0$ from below (left) :
$\lim\limits_{x \to x_0^-} f(x) = \left. \lim\limits_{x_0} f \right|_{I \cap ] -\infty, x_0[} = l$
*)

Section limit_one_sided_def.

Definition limitAbove (f : PartFunct R)(x0 l : R) : Prop :=
    real x0 -> limit (restriction R f (fun (x:R) => x > x0)) x0 l.

Definition limitBelow (f : PartFunct R)(x0 l : R) : Prop :=
    real x0 -> limit (restriction R f (fun (x:R) => x < x0)) x0 l.


End limit_one_sided_def.

End Limit_definitions.

(**
We the previous definitions, it's likely to have an hypothesis : 
[H0 : forall (x_inf : R_inf x), match x_inf with
    | xReal ..  | pInf ..   | mInf ...]
We define the following tactic to simplify such an hypothesis with an extra hypothesis (such as
[H1 : pInfinite x], [H1 : mInfinite x] or [H1 : real x]) :
*)

Ltac simplify_inf :=
    repeat match goal with
        | [ H : forall (a : R_inf ?x), match a with | pInf _ => _ | mInf _ => _ | xReal _ => _ end |- _] => 
            let name := fresh in 
                match goal with
                    | [ H1 : pInfinite x |- _ ] => pose proof (H (pInf x H1)) as name ; simpl in name ; clear H
                    | [ H1 : mInfinite x |- _ ] => pose proof (H (mInf x H1)) as name ; simpl in name ; clear H
                    | [ H1 : real x |- _ ] => pose proof (H (xReal x H1)) as name ; simpl in name ; clear H
                    | _ => fail
                end
        | [ H : predicate_neighbourhood ?a ?b ?c |- _ ] => unfold predicate_neighbourhood in H
        | _ => fail
    end.

(**
* Theorems
*)

Section Limit_theorems.

Variable f : PartFunct R.
Let I := Dom R f.

(**
If the function $$f(x)$$ has a limit when $$x$$ approaches $$x_0$$, then this limit is unique.
*)

Section limit_unique.

(**
We only deal with the case $$x_0 \in I$$ or $$x_0$$ is a bound of $$I$$.
*)
Variable x0 : R.
Hypothesis Hx0 : adherent_point x0 I.

Lemma limit_uniqueness_not_empty (d1 d2 : R) : d1 >0 -> d2 > 0 -> 
    not_empty R ( Inter R, [ (fun x => Rabs (x - x0) < d1) (fun x => Rabs (x - x0) < d2) I ]) .
Proof.
    (* Unfold the definitions *)
    intros. unfold adherent_point in Hx0. unfold not_empty.
    (* We pose $$\delta = \min \{ \delta_1, \delta_2 \}$$, and it satifies the whole intersection. *)
    pose (d := Rmin d1 d2). hintro Hx0 d ; assert (d > 0) by (now apply Rmin_pos) ; hintro Hx0 H1 ;destruct Hx0.
    (* Then, we just unfold the intersection, and use the [Rmin] properties [Rmin_l] and [Rmin_r] *)
    exists x ; destruct H2 ; unfold_subsets.
        assert (d <= d1) by apply Rmin_l. apply Rlt_le_trans with (r2 := d) ; auto.
        assert (d <= d2) by apply Rmin_r. apply Rlt_le_trans with (r2 := d) ; auto.
        assumption.
Qed.
Check uniqueness.
Theorem limit_uniqueness : limitExists f x0 -> forall (l1 l2 : R), (limit f x0 l1 /\ limit f x0 l2) <-> l1 = l2 /\ (limit f x0 l1 \/ limit f x0 l2).
Proof.
    intros H l1 l2. iff_reasoning ; intros ; destruct H0 ; split ; [idtac | now left | idtac | idtac].
    (* First implication *)
        (* There are 27 cases. We only prove< the case $$x_0 \in \mathbb{R}$$ and $$l \in \mathbb{R}$$ *)
        inf_cases x0 ; [admit | admit | inf_cases l1 ; [admit | admit | inf_cases l2 ; [admit | admit | idtac]]].
        (* We reason by the absurd (we suppose [l1 <> l2]). We deal with the case [l1 < l2] *)
        absurd_reasoning ; different_cases H5 ; [idtac | admit].
        (* Unfold the definition of the limits : for both we pose $$\epsilon = \frac{l_2 - l_1}{2} *)
        unfold limit in H0, H1 ; simplify_inf. pose (e:= (l2 - l1) / 2 // R2_neq_R0) ; hintro H5 e ; hintro H1 e.
        (* We prove that $$\epsilon > 0$$ *)
        assert (e>0). assert (l2 - l1 > 0). apply Rlt_gt in H6 ; now apply Rgt_minus in H6. assert (2 > 0) by fourier. 
          apply (RDiv_pos_pos (l2 - l1) 2 R2_neq_R0 H0 H7). hintro H1 H0 ; hintro H5 H0 ; simplify_inf. 
          destruct H7, H5 ; rename x into d1 ; rename x1 into d2. destruct H1, H5.
        (* We choose an $$x \in ]x_0 - d_1, x_0 + d_1[ \cap ]x_0 - d_2, x_0 + d_2[ \cap I$$.*)
            (* This interval is not empty because $$d_1 > 0$$ and $$d_2 > 0$$ *)
            assert (not_empty R ( Inter R, [ (fun x => Rabs (x - x0) < d1) (fun x => Rabs (x - x0) < d2) I ])) by
              apply (limit_uniqueness_not_empty d1 d2 H1 H5). destruct H9. destruct H9 ; destruct H10 ; destruct H11 ; clear H12.
            (* We can then apply this [x] to H7 and H8 *)
            hintro H7 x ; hintro H8 x ; hintro H7 H11 ; hintro H8 H11 ; hintro H7 H9 ; hintro H8 H10.
            (* First, rewrite the hypothesis $$|f(x) - l_1| \leq \epsilon$$ into $$|l_1 - f(x)| \leq \epsilon$$ *)
            assert (l1 - (f x H11) = -(f x H11 - l1)) by ring. rewrite <- Rabs_Ropp in H8 ; rewrite <- H12 in H8. clear H12.
            (* We then have $$|l_2 - l_1| = |-(f(x) - l_2) - (f(x) - l_1)|$$. With the triangle inequality we
            then have $$|l_2 - l_1| \leq |f(x) - l_2| + |f(x) - l_1|$$. With the definition of $$\epsilon$$, it
            comes $$|l_2 - l_1| \leq 2 \epsilon = l_2 - l_1$$ *)
            assert ( Rabs (l1 - l2) >= Rabs (l1 - l2)) by apply Rle_refl.  pattern (l1 - l2) at 1 in H12.
              assert (l1 - l2 = (l1 - (f x H11)) + ((f x H11) - l2)) by ring.
              rewrite H13 in H12. apply Rge_le in H12. clear H13.
              assert ( Rabs (l1 - f x H11 + (f x H11 - l2)) <= Rabs (l1 - f x H11) + Rabs (f x H11 - l2)) by apply Rabs_triang.
              assert (Rabs (l1 - l2) <= Rabs (l1 - f x H11) + Rabs (f x H11 - l2)). 
                apply Rle_trans with (r2:= Rabs (l1 - f x H11 + (f x H11 - l2))) ; auto. clear H12 H13.
              apply (Rlt_rewrite_le_r _ _ _ _ H7) in H14 ; rewrite Rplus_comm in H14 ; apply (Rlt_rewrite_lt_r _ _ _ _ H8) in H14.
            (* $$|l_1 - l_2| \leq 2 \epsilon = l_2 - l_1$$ is clearly a contradiction *)
            rewrite <- double in H14 ; unfold e in H14 ; rewrite RDiv_simpl in H14.
                (* We can rewrite it as $$l_2 - l_1 < l2 - l1$$, because $$l_2 > l_1$$ *)
                assert (l1 - l2 < 0) by auto with real. rewrite (Rabs_left _ H12) in H14 ; clear H12.
                (* Highlight the contradiction *)
                assert (- (l1 - l2) = l2 - l1) by ring. rewrite H12 in H14 ; clear H12. now apply (Rlt_asym (l2 - l1) (l2 - l1)).
    (* Reciprocal : We have [l1 = l2], so we just have to rewrite. *)
        elim H1 ; intros ; auto. pattern l2 in H2. now rewrite <- H0 in H2.
        elim H1 ; intros ; auto. pattern l1 in H2. now rewrite H0 in H2.
Qed.

(**
We define this helper lemma : when we have an hypothesis [H : limit f x0 l1] and the goal [limit f x0 l2], then
we try to prove [l1 = l2]. (For this, just [apply limits_equals H]
(This lemma might usally be used with an [assert] first)
*)

Lemma limits_equals : forall (l1 l2 :R), limit f x0 l1 -> (~ limit f x0 l2) -> (~ l1 = l2).
Proof.
    (* The lemma is just a translation of the previous theorem [limit_uniqueness] 
    intros. assert (limitExists f x0) by (now exists l1). red. intro. elim H0. apply (limit_uniqueness H1 l1 l2 H). Check . 

apply limit_uniqueness in H.
apply (limit_uniqueness) in H1. unfold uniqueness in H1. hintro H1 l1. hintro H1 l2. hintro H1 H.
    intros ; apply limit_uniqueness ; auto. now exists l1.
Qed.*)
Admitted.

End limit_unique.

(**
If [f] is defined in $$x_0 \in I$$ and $$\lim\limits_{x_0} f$$ exists, then $$\lim\limits_{x_0} = f(x_0)$$.
*)

Theorem finite_limit_value : forall (x0 : R)(Hx0 : I x0), real x0 -> limitExists f x0 -> limit f x0 (f x0 Hx0).
Proof.
    intros ; unfold limitExists in H0 ; destruct H0 ; rename x into l.
    (* We deal with the 3 possible cases : $$l = +\infty$$, $$l \in \mathbb{R}$$ or $$l = -\infty$$ *)
    assert ( pInfinite l \/ mInfinite l \/ real l) by (apply reals_infinity) ; destruct H1.
      (* Case : $$l = +\infty$$ *)
        unfold limit in H0 ; simplify_inf.
        (* We pose $$A = f(x_0) + 1$$, and $$x = x_0$$, and then we have the contradication $$f(x_0) \geq f(x_0) + 1$$ *)
        hintro H2 (f x0 Hx0 + R1). simplify_inf.  destruct H0. rename x into d. destruct H0. hintro H2 x0. hintro H2 Hx0.
        assert (f x0 Hx0 >= f x0 Hx0 + R1). apply H2. assert (x0 - x0 = 0) by ring ; rewrite H3. rewrite Rabs_R0. now apply Rgt_lt.
        assert (1 <= 0) by fourier. apply Rle_not_gt in H4. elim H4. fourier.
    destruct H1.
      (* Case : $$l = -\infty$$ *)
        unfold limit in H0 ; simplify_inf.
        (* We pose $$A = f(x_0) - 1$$, and $$x = x_0$$, and then we have the contradication $$f(x_0) \leq f(x_0) - 1$$ *)
        hintro H2 (f x0 Hx0 - R1). simplify_inf.  destruct H0. rename x into d. destruct H0. hintro H2 x0. hintro H2 Hx0.
        assert (f x0 Hx0 <= f x0 Hx0 - R1). apply H2. assert (x0 - x0 = 0) by ring ; rewrite H3. rewrite Rabs_R0. now apply Rgt_lt. 
        assert (1 <= 0) by fourier. apply Rle_not_gt in H4. elim H4. fourier.
      (* Case : $$l \in \mathbb{R}$$ *)
        assert (limitExists f x0)by now exists l.
        (* We reason by the absurd : then we prove that $$f(x_0) \neq l$$ is impossible *)
        absurd_reasoning. assert (l <> (f x0 Hx0)). intro. assert (limit f x0 (f x0 Hx0)).
          apply <- (limit_uniqueness x0 (adherent_point_in I x0 Hx0) H2 l (f x0 Hx0)) ; split ; [auto | now left]. contradiction.
        (* We unfold $$\lim\limits_{x_0} f = l$$ by posing $$\epsilon = \frac{|l - f(x_0)|}{2}$$ *)
        unfold limit in H0. simplify_inf. pose (e:= (Rabs (l - (f x0 Hx0))) / 2 // R2_neq_R0). hintro H5 e.
        (* We prove that $$|l - f(x_0)| > 0$$ and that $$2 >0$$ *)
        assert (Rabs (l - f x0 Hx0) > 0). assert (l - f x0 Hx0 <> 0) by now apply Rminus_eq_contra. 
          now apply Rabs_pos_lt. assert (2>0) by fourier. 
        (* We prove that $$\epsilon > 0$$ *)
        assert (e > 0). now apply RDiv_pos_pos. hintro H5 H7 ; simplify_inf; destruct H8 ; destruct H5 ; rename x into d.
        (* We also prove that $$\epsilon < |l - f(x_0)|$$, so $$f(x_0) \not\in [l - \epsilon, l + \epsilon]$$ *)
        assert (e < Rabs (l - f x0 Hx0)) by now apply RDiv_2_lt. 
        (* Or, $$x_0 \in [x_0 - \delta, x_0 + \delta] \cap I$$, so we have a contradiction *)
        hintro H8 x0. hintro H8 Hx0. assert (x0 - x0 = 0) by ring ; rewrite H10 in H8 ; rewrite Rabs_R0 in H8. hintro H8 H5.
          rewrite Rabs_minus_sym in H9. apply Rlt_not_ge in H9. apply Rlt_gt in H8 ; apply Rgt_ge in H8 ; contradiction.
Qed.

(**
Sequential characterization of a limit
*)

(*Hypothesis x0 : IR_inf.
Hypothesis l l' : IR_inf.
Hypothesis f : CSetoid_un_op IR.
Hypothesis u v w : CSetoid_un_op IR.
Hypothesis lr : IR.

Theorem sequential_limit : (forall (L : limit), limitProp f L -> limit_variable L = x0 -> limit_value L = l)
    <-> (forall (Un : nat->IR), forall (L fL : Un_limit), Un_limitProp Un L -> Un_limitProp (fun n => f (Un n)) fL 
        -> Un_limit_value L = x0 -> Un_limit_value fL = l).
Admitted.

Theorem inequality_limit : forall (L L' : limit), limitProp u L -> limitProp v L' 
    -> predicate_neighbourhood (fun x => (u x) [<=] (v x)) x0 -> le_IR_inf l l'.
Admitted.

Theorem squeeze_theorem : (u --x0-->lr) -> (v --x0-->lr)
    -> predicate_neighbourhood (fun x => ((u x) [<=] (v x)) /\ ((v x) [<=] (w x))) x0
    -> (v --x0-->lr).
Admitted.*)

End Limit_theorems.



