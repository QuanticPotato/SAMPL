(***********************************************************************
*  ____   __   _  _  ____  __    *     Still Another Math library !    *
* / ___) / _\ ( \/ )(  _ \(  )   *-------------------------------------*
* \___ \/    \/ \/ \ ) __// (_/\ *        (c) Chauvin Barnabé          *
* (____/\_/\_/\_)(_/(__)  \____/ *  This file is distributed under the *
*                                *  terms of the GPL License Version 2 *
***********************************************************************)

(**
* Classical logic
*)

Require Export Logic.
Require Export Classical_Prop.
Require Export ClassicalFacts.
Require Export Setoid.
Require Export FunctionalExtensionality.

(**
** Classical axioms
In the whole project, we reason with classical logic. That's why we admit the following axioms :
- Law of the excluded middle : $$P \lor \lnot P$$
- Proof by contradiction : $$\lnot \lnot P \Rightarrow P$$
- Contraposition : $$(\lnot B \Rightarrow \lnot A) \vdash (A \Rightarrow B)$$
- Material conditional : $$(A \Rightarrow B) \equiv (\lnot A \lor B)$$
For now, we use the definitions in the stdlib for these axioms.

We also admit the degeneracy axiom (Every proposition is either [True] or [False]
*)

Axiom degeneracy : prop_degeneracy.

(**
We define a helper tacti [double_neg], to be used with the [rewrite] tactic. (It's just a
translation of the [NNPP] lemma)
*)

Lemma NNPP_rec : forall P:Prop, P -> (~ ~ P).
Proof.
    unfold not ; intros ; elim (classic P) ; auto.
Qed.
Hint Resolve NNPP_rec: core.

Lemma double_neg_iff (P : Prop) : P <->  (~ ~ P).
Proof.
    intros ; unfold iff ; split ; intros ; [now apply NNPP_rec | now apply NNPP].
Qed.

Theorem double_neg (P : Prop) : P = (~ ~ P).
Proof.
    apply prop_degen_ext ; [exact degeneracy | exact (double_neg_iff P) ] .
Qed.

(**
** Reasoning tactics
*)

(**
A simple tactic that allow to do proofs by contradiction, as in classical mathmematics
*)

Ltac absurd_reasoning :=
    match goal with 
        | _  => apply NNPP ; intro
    end.

(**
When proving uniqueness, we often use an absurd reanning (i.e. suppose that two object
satisfy a predicate, and prove they are equal). The following tactic allow to do this easily :
*)

Ltac uniqueness_reasoning n1 n2 H1 H2 :=
    intros ; unfold uniqueness ; intros n1 n2 H1 H2.

(**
To prove a "if and only if" statement, we prove the two implications :
(The tactic apply to the current goal)
*)

Ltac iff_reasoning :=
    intros ; unfold iff ; split.

(**
** Qantification
We here define equivalence between $$\forall$$ and the negation of $$\exists$$, 
and vice versa.
*)

Theorem neg_quantif_ex (T:Type)(P:T->Prop) : (~ (exists (x:T), P x)) <-> (forall (x:T), ~ P x).
Proof.
    (* For the two implications, we reason be the absurd *)
    iff_reasoning ; intros ; absurd_reasoning ; [
        destruct H ; exists x ; now apply NNPP in H0
        | apply NNPP in H0 ; destruct H0 ; pose proof (H x) ; contradiction].
Qed.
Hint Resolve neg_quantif_ex: core.

Theorem neg_quantif_forall (T:Type)(P:T->Prop) : (~ (forall (x:T), P x)) <-> (exists (x:T), ~ P x).
Proof.
    iff_reasoning ; intros ; absurd_reasoning.
    (* First implication *)
      (* We use the former theorem : [neg_quantif_ex] *)
        (* For this, we use a proposition [Q] (such that $$Q \equiv \lnot P$$) in [H] *)
        pose (Q:=fun x=> ~ P x) ; assert ((fun x : T => ~ Q x) = P) ; unfold Q. replace P with (fun x=> P x) ;
          [idtac|auto] ; apply functional_extensionality_dep ; intro ; now rewrite <- double_neg.
          replace P with (fun x=>~ Q x) in H. 
        (* We can the use the theorem *)
        rewrite <- (neg_quantif_ex T Q) in H ; rewrite <- double_neg in H. destruct H.
      (* We can then eliminate [H0] because we have a witness [x] that satisfies $$\lnot P \equiv Q$$ *)
        elim H0. exists x ; now unfold Q in H.
    (* Reciprocal : With the absurd reasoning, we just have to eliminate the double negation. *)
        rewrite <- double_neg in H0. destruct H ; pose proof (H0 x) as H1 ; contradiction.
Qed.

(*Ltac neg_quantif H :=
     let rec neg_quantif_type Htype := 
         match Htype with
             | ~ ?P => neg_quantif_type P
             | forall (_ : ?T), ?P _ => idtac "forall"
             | _ => fail
         end
     in
         match type of H with
             | ?P => neg_quantif_type P
         end. *)

(**
* Useful proof tactics
*)

(**
The tactic [hintro] apply to an hypothesis of the form [forall (x:T), ...].
Usage : [hintro H y] (where [y] is of type [T]) : it replaces every occurences of [x] by [y].
*)

Ltac hintro H y:=
    let Htmp := fresh in
        match type of H with
            | forall b:_, ?a => rename H into Htmp ; pose proof (Htmp y) as H ; clear Htmp
            | _ => idtac "Hypothesis must have the form [forall ...] !" ; fail
        end.

(**
The [[apply_connector]] allows to apply the same Lemma/Theorem/Axiom on several terms of
a [[t1 \/ t2 \/ t3]], or a [[t1 /\ t2 /\ t3]]
*)

Lemma apply_or_prop : forall (P Q P' Q' : Prop), P \/ Q -> (P -> P') -> (Q -> Q') -> (P' \/ Q').
Proof.
   tauto.
Qed.

Lemma apply_and_prop : forall (P Q P' Q' : Prop), P /\ Q -> (P -> P') -> (Q -> Q') -> (P' /\ Q').
Proof. 
    tauto. 
Qed.

Ltac apply_connector H e r :=
    match type of H with
        | ?A \/ ?B => apply (apply_or_prop _ e r)
    end.

Ltac Zcases_on_value z x :=
    match goal with 
        | [ Hcases_on_value : {z = x} + {z <> x} |- _ ] => destruct Hcases_on_value
    end.

Ltac getConclusion lemma :=
    match goal with
        (*| _ -> ?B => idtac*)
        | [ H:_ |- _] => idtac
    end.
