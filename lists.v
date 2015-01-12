Require Import List.

(**
This file regroup useful stuff about list that I didn't find in standard library
*)

(**
* List creation
*)

(**
** Create a list from a sequence
*)

Section List_creation.

Variables A B : Type.

(*Fixpoint list_from_seq (seq : A->B) (inc : A->A) (first:A) (last : A) : (list B) :=
    match first with
        | last => nil
        | _ => (seq first)::(list_from_seq seq (inc A) last)
    end.*)

End List_creation.

(**
* Operations
*)

(**
** Applying functions to the elements of list(s)
*)

Section List_map.

Variable A : Type.
Variable f : A->A->A.

(**
[list_map] is the equivalent of [map] defined in the stdlib (Coq.Lists.List).
(We redefine it here to avoid including several files on the lists)
*)

Fixpoint list_map (f : A->A) (l : list A) : list A := map f l.

(**
[list_map2] is in some ways the equivalent of the previous [list_map], but it allows to apply functions
to the corresponding elements of two lists.
*)

Fixpoint list_map2 (l l' : list A) (default : A) {struct l} : list A :=
    match l, l' with
        | nil, nil => nil
        | nil, a::t => map (fun (x:A) => (f x default)) t
        | a::t, a'::t' => cons (f a a') (list_map2 t t' default)
        | a::t, nil => cons (f a default) (list_map2 t nil default)
    end.

End List_map.


(**
** Apply a condition to every elements of the list
(This section is inspired from MathClasses)
*)

Section List_predicate.

Variable A : Type.
Variable P : A->Prop.

(**
[list_predicate] test every elements of the list to check whether they satisfty the predicate [P].
It creates a new list of [Prop], corresponding to the predicate results of every elements.
*)

Definition list_predicate (l : list A) : list Prop := map P l.

(**
[list_all_predicate] is True if and only if every elements of the list satisfy the predicate [P].
*)

Definition list_all_predicate (l : list A) : Prop := 
    fold_left and (list_predicate l) True.

(**
[list_all_predicate] is True if and only if at least one element of the list satisfy the predicate [P].
*)

Definition list_one_predicate (l : list A) : Prop :=
    fold_left or (list_predicate l) False.

End List_predicate.
