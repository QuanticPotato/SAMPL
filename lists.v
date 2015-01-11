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

(*Variables A B : Type.
Definition eq_bool (x y : A) :bool := (x = y) -> true.

Fixpoint list_from_seq (seq : A->B) (inc : A->A) (first:A) (last : A) : (list B) :=
    if (eq_bool first last) then nil
    else (seq first)::(list_from_seq seq (inc A) last).*)

End List_creation.

(**
* Operations
*)

(**
** Applying functions to the elements of two lists
(This is in some ways the equivalent of the List.Map section in the standard library, but it allows to apply functions
to the corresponding elements of two lists)
*)

Section List_map2.

Variable A : Type.
Variable f : A->A->A.

Fixpoint list_map2 (l l' : list A) (default : A) {struct l} : list A :=
    match l, l' with
        | nil, nil => nil
        | nil, a::t => map (fun (x:A) => (f x default)) t
        | a::t, a'::t' => cons (f a a') (list_map2 t t' default)
        | a::t, nil => cons (f a default) (list_map2 t nil default)
    end.

End List_map2.
