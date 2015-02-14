(**
* Classical logic
*)

(**
In the whole project, we reason with classical logic. That's why we admit the following axioms :
- Law of the excluded middle : $$P \lor \lnot P$$
- Proof by contradiction : $$\lnot \lnot P \Rightarrow P$$
- Contraposition : $$(\lnot B \Rightarrow \lnot A) \vdash (A \Rightarrow B)$$
- Material conditional : $$(A \Rightarrow B) \equiv (\lnot A \lor B)$$
*)

(**
For now, we use the definitions in the stdlib for this axioms
*)

Require Export Logic.
Require Export Classical_Prop.

(**
A simple tactic that allow to do proofs by contradiction, as in classical mathmematics
*)

Ltac absurd_reasonning :=
    match goal with 
        | _  => apply NNPP ; intro
    end.

(**
* Useful tactics
*)

(**
The [[apply_connector]] allows to apply the same Lemma/Theorem/Axiom on several terms of
a [[t1 \/ t2 \/ t3]], or a [[t1 /\ t2 /\ t3]]
*)

Section apply_or.

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

End apply_or.
