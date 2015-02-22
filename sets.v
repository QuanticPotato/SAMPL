Require Export SAMPL.logic.

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
*)

Section subsets_operations.

Variable A B C : E -> Prop.

Definition union : E->Prop := fun (x:E) => A x \/ B x.
Definition inter : E->Prop := fun (x:E) => A x /\ B x.

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

End Sets_definitions.

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
