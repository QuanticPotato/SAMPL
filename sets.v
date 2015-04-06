(***********************************************************************
*  ____   __   _  _  ____  __    *     Still Another Math library !    *
* / ___) / _\ ( \/ )(  _ \(  )   *-------------------------------------*
* \___ \/    \/ \/ \ ) __// (_/\ *        (c) Chauvin Barnabé          *
* (____/\_/\_/\_)(_/(__)  \____/ *  This file is distributed under the *
*                                *  terms of the GPL License Version 2 *
***********************************************************************)

Global Generalizable All Variables.

Require Export SAMPL.lists.

(**
* Definition
In the whole project, subset of [E] will be represented with a predicate
of type [E -> Prop], that whether an element belongs to the subset.
For this purpose, we define the following notation : 
$$\{ x || P\} \equiv \{ x \in \mathbb{R} \mid P(x) \}$$.
*)

Notation " { x '||' P } " := (fun (x:_) => P x) (at level 0, x at next level).

Section Sets_definitions.

Variable E:Type.

(**
** Operations
We define the union and the intersection of two subsets as follows : 
- Union : $$A \cup B = \{ x \in E \mid x \in A \lor x \in B \}
- Intersection : $$A \cap B = \{ x \in E \mid x \in A \land x \in B \}
- Subset : $$A \subset B$$ if $$\forall x \in A, x \in B$$.
*)

Section subsets_operations.

Variable A B C : E -> Prop.

Definition union : E->Prop := fun (x:E) => A x \/ B x.
Definition inter : E->Prop := fun (x:E) => A x /\ B x.

Definition subset := forall (x:E), A x -> B x.

(**
At the end of the file (In order to have a global scope), we define the notation
[Inter] and [Union], that respectively correspond to the intersection and the union
of several subsets.
*)

End subsets_operations.

(**
** Non-emptiness
*)

(**
A subset [I] of [E] is not_empty if it exists an element of [E] that satisfies
the predicate [I].
*)

Section subsets_nonemptiness.

Variable A B C : E -> Prop.

Definition not_empty (I : E -> Prop) := exists (x:E), I x.

End subsets_nonemptiness.

(**
** Sigma-types
We use the definition [sig] of the standard library to define types associated with 
subset predicates.
*)

Section sigmatypes.

Variable Iprop : E -> Prop.

(**
We define an injection from the subset to the carrier type. (It might be useful in
definitions to avoid any type problems)
*)

Definition sig_injection := @proj1_sig E Iprop.

Let inj := sig_injection.
Let I:= sig Iprop.

(**
The [exist] constructor of the [sig] type is the opposite of our [sig_injection].
Thus, the expression [sig (exist ...)] might be simplified : 
*)

Lemma sig_simpl : forall `(Reflexive E R) (x:E)(Hx : Iprop x), R (inj (exist Iprop x Hx)) x.
Proof.
    intros. unfold inj. unfold sig_injection. unfold proj1_sig. reflexivity.
Qed.

Definition full_sig := forall (x:E), Iprop x.

Lemma full_sig_comp (P : E->Prop) : full_sig -> (forall (x:E), P x) -> (forall (x:I), P (inj x)).
Admitted.
End sigmatypes.

End Sets_definitions.

(**
In proofs, it may be redundant to have a lot of the previous injection.
Hence, we define the tactic [inj_replace inj x y] (where [inj] is of type [I -> E]) : 
it replaces every occurences of [x] that is applied to the injection [I -> E] with a 
new witness (named [y]) of the same value and of type [E].
*)

Ltac inj_replace inj x y :=
    match type of inj with 
        | ?A -> ?B => pattern (inj x) ; pose (y:= (inj x)) ;
            replace (inj x) with y ; [idtac | auto]
        | _ => idtac "[inj] does not seem to be a valid injection !"
    end.

(**
We also define the tactic [inj_replace_all inj] (where [inj] is still of type [I->E]) :
it replaces every occurences of [inj _], applying the previous tactic.
*)
Ltac  inj_replace_next inj :=
  match goal with
  | [ |- context[inj ?t] ] => let t' := fresh "t" in inj_replace inj t t'
  end.
Ltac inj_replace_all inj := repeat inj_replace_next inj.

(**
* Notations
*)

(**
We define notations to be able to use intersection (or union) of several subsets :
*)

Notation "'Inter' Typ , [ x .. y ]" := (inter Typ x .. (inter Typ y (fun z => True)) ..)
    (at level 0, x at next level).

Notation "'Union' Typ , [ x .. y ]" := (union Typ x .. (union Typ y (fun z => True)) ..)
    (at level 0, x at next level).

(**
We also define a tactic [unfold_subsets] to unfold these notations. 
If it is an intersection, it [split] the result and by the way remove the trailling [/\ True].
*)

Ltac unfold_subsets :=
    try unfold inter ; try unfold union ; 
    match goal with 
        | [ |- _ /\ _] => repeat split
        | [ |- _ \/ _] => idtac 
        | _ => idtac 
    end.
