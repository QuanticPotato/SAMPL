(***********************************************************************
*  ____   __   _  _  ____  __    *     Still Another Math library !    *
* / ___) / _\ ( \/ )(  _ \(  )   *-------------------------------------*
* \___ \/    \/ \/ \ ) __// (_/\ *        (c) Chauvin Barnabé          *
* (____/\_/\_/\_)(_/(__)  \____/ *  This file is distributed under the *
*                                *  terms of the GPL License Version 2 *
***********************************************************************)

Require Export SAMPL.structures.

Global Generalizable All Variables.

(**
* Definitions
*)

(**
** Vector-space and vector-subspace structures
We call a vector-space over $$\mathbb{K}$$ is an abelian group $$E$$ with two operations (a classical
addition (of the $$E$$ structure usually) and a scalar multiplication, that satisfy the 
eight following axioms :
- Associativiy of addition : $$\forall u ,v, w \in E, u + (v + w) = (u + v) + w$$
- Commutativity of addition : $$\forall u, v \in E, u + v = v + u$$
- Identify element of addition : $$\exists 0_E \in E$$, \forall v \in E, v + 0_E = v$$.
We call this element the zero vector.
- Inverse elements of addition : $$\forall v \in E, \exists -v \in E, v + (-v) = 0_E$$.
We call this element the additive inverse.
- Compatibility of scalar multiplication with field multiplication : 
$$\forall a, b \in \mathbb{K}, \forall v \in E, a(b\cdot v) = (ab)v$$
- Identify element of scalar multiplication : 
$$\exists 1_\mathbb{K} \in \mathbb{K}, \forall v \in E, 1_\mathbb{K} v = v$$. We call this
element the multiplicative identify.
- Distributivity of scalar multiplication with respect to vector addition : 
$$\forall a \in \mathbb{K}, \forall u, v \in E, a(u + v) = au + av$$
- Distributivity of scalar multiplication with respect to field addition :
$$\forall a, b \in \mathbb{K}, \forall v \in E, (a + b)v = av + bv$$
*)

Section vector_space_def.

(**
We first define the scalar multiplication. 
The addition is already defined : we use [Plus] of a semiring.
*)

Class ScalarMult K E := scalar_mult : K -> E -> E.

Context K {Ke : Equiv K} {Kplus : Plus K} {Kmult : Mult K} {Kzero : Zero K} {Kone : One K}
    {Knegate : Negate K} {Kap : Apart K} {Krecip : Recip K} {Kf : Field K}.

Context E {Ee : Equiv E} {Eplus : Plus E} {Ezero : MonUnit E} {Eopp : Negate E} {Eg : AbGroup E}.

Context {SV_Mult_H : ScalarMult K E}.

(**
We must define the 4 last axioms, and then we can define the structure itself :
*)

Class ScalarMultCompatibility : Prop := 
    scalar_mult_comp : forall (a b : K)(v : E), scalar_mult a (scalar_mult b v) = scalar_mult (a * b) v.

Class ScalarMultDistr_Vector : Prop := scalar_mult_distr_vector : 
    forall (a : K)(u v : E), scalar_mult a (sg_op u v) = sg_op (scalar_mult a u) (scalar_mult a v).

Class ScalarMultDistr_Field : Prop := scalar_mult_distr_field : 
    forall (a b : K)(v : E), scalar_mult (a + b) v = sg_op (scalar_mult a v) (scalar_mult b v).

Class VectorSpace : Prop := {
    vs_add_ass : Associative Eplus ;
    vs_add_comm : Commutative Eplus ;
    vs_add_id : LeftIdentity Eplus Ezero ;
    vs_add_inv : Negate E ;
    vs_scalar_mult_comp : ScalarMultCompatibility ;
    vs_scalar_mult_id : LeftIdentity scalar_mult one ;
    vs_scalar_mult_distr_vector : ScalarMultDistr_Vector ;
    vs_scalar_mult_distr_field : ScalarMultDistr_Field
}.

End vector_space_def.

Infix "[x]" := scalar_mult (at level 40).

(**
We now define three properties that allow to define a lot of vector spaces :
- Let $$\mathbb{L}$$ be a field, such that $$\mathbb{K} \subset \mathbb{L}$$ (So $$1_\mathbb{K} = 1_\mathbb{L}$$).
Then $$\mathbb{L}$$ is a vector space over $$\mathbb{K}$$.
-
*)

Section vector_space_charac_1.

Variable L : Set.
Context {Le : Equiv L} {Lplus : Plus L} {Lmult : Mult L} {LmultAssoc :Associative Lmult} {Lzero : Zero L} {Lone : One L}
    {Lnegate : Negate L} {Lap : Apart L} {Lrecip : Recip L} {Lf : Field L}.

Variable Kprop : L->Prop.
Let K := sig Kprop.
Let inj := sig_injection L Kprop.

Hypothesis Hplus_closed : ClosedOp L Kprop plus.
Hypothesis Hmult_closed : ClosedOp L Kprop mult.

Hypothesis Hone : Kprop Lone.

Instance L_scalarMult : ScalarMult K L := (fun x y => Lmult (inj x) y).
Instance Kone : One K := Fone L Kprop Hone.
Context {Kzero : Zero K} {Knegate : Negate K} {Kap : Apart K} {Krecip : Recip K}
    {Ksf : (@SubField L Kprop Le Lplus Hplus_closed Lmult Hmult_closed Kone Knegate Kap Kzero Krecip)}.
(*
Context {H:Fone}.
Lemma test : VectorSpace K L.
Proof.
    (* The first 4 axioms of the additions (It is the internal addition of [L], so it does not change) *)
    split. apply _. apply _. apply _. apply _.
    (* We unfold the definitions, and then we use functional extensionality *)
    (* TODO : do it with classes features ! *)
    unfold ScalarMultCompatibility ; unfold scalar_mult ; intros ; unfold L_scalarMult. 
      repeat rewrite spec_mult_restr ; unfold Associative in LmultAssoc ; unfold HeteroAssociative in LmultAssoc.
      rewrite LmultAssoc.  (* TODO *) admit.
    unfold LeftIdentity. unfold scalar_mult. unfold L_scalarMult. intros. unfold one.
    *)

End vector_space_charac_1.

(**
We define a vector subspace (also called a linear subspace).
Let $$E$$ be a vector space over $$\mathbb{K}$$, and $$F \subset E$$. $$F$$ is a vector subspace 
of $$E$$ if :
- $$F$$ is closed under addition : $$\forall x, y \in F, x + y \in F$$
- $$F$$ is closed under scalar multiplication : 
$$\forall \lambda \in \mathbb{K}, \forall x \in F, \lambda x \in F$$
- The restriction of the addition of $$E$$ to $$\mathbb{K} \times E$$ let $$F$$ be a vector space 
over $$\mathbb{K}$$ (i.e. $$F$$ satisfy the vector space axioms)
We define the subset $$F$$ with the same way we did in sets.v (i.e a predicate [E->Prop]).
*)

Section vector_definitions.

Context (K:Set) {Ke : Equiv K} {Kplus : Plus K} {Kmult : Mult K} {Kzero : Zero K} {Kone : One K}
    {Knegate : Negate K} {Kap : Apart K} {Krecip : Recip K} {Kf : Field K}.

Context (E:Set) {Ee : Equiv E} {Eadd : Plus E} {Ezero : Zero E} {Eneg : Negate E} {Eg : AbGroup E}
    {Emult : ScalarMult K E} {Eh : VectorSpace K E}.

Section vector_subspace_def.

Variable Fprop : E -> Prop.
Let F := sig Fprop.
Let inj_F_E := @proj1_sig E Fprop.

(**
We first define the "closed operation" propositions :
*)

Class ClosedIntOp : Prop := closed_internal_op : forall (x y : F), Fprop (Eadd (inj_F_E x) (inj_F_E y)).
Class ClosedExtOp : Prop := closed_external_op : forall (l : K)(x : F), Fprop (Emult l (inj_F_E x)).

Context `{VectorSpace K F}.

Class VectorSubspace : Prop := {
    vss_add_closed : ClosedIntOp ;
    vss_mult_closed : ClosedExtOp ;
    vss_add (x y : F) := exist Fprop (Eadd (proj1_sig x) (proj1_sig y)) (closed_internal_op x y) ;
    vss_mult (l:K)(x:F) := exist Fprop (Emult l (proj1_sig x)) (closed_external_op l x) ;
    (* Axioms of a vector space *)
    vss_axioms : VectorSpace K F
}.

(**
We define two characterizations (or "useful criteria") to prove that a subset [F] is a vector subspace :
(These criterias consist in a fewer list of axioms)
- Criteria 1 : 
  - ($$F \subset E$$. This is obvious with our definition of $$F$$, wo we don't define it.)
  - $$F \neq \emptyset$$ (We usually prove that the zero vector is included in $$F$$)
  - $$\forall x, y \in F, x + y \in F$$
  - $$\forall x \in F, \forall \lambda \in \mathbb{K}, \lambda x \in F$$
- Criteria 2 : (It only concises the two last axioms of the latter criteria)
  - $$\forall x, y \in F, \forall \lambda \in \mathbb{K}, \lambda x + y \in F$$
*)

(* TODO *)

End vector_subspace_def.

(**
** Examples
In this section, we give several example of vector-spaces and vector-subspaces
We'll deal with the following vector-spaces : 
- Geometrical vectors : $$\mathbb{R}^2$$ and $$\mathbb{R}^3$$ over $$\mathbb{R}$$ (denoted by [Ev2] and [Ev3])
- $$\mathcal{F}(\mathbb{R}, \mathbb{R})$$ over $$\mathbb{R}$$ (denoted by [Ef])
We first prove they are actual vector-spaces, and then we use them to define vector-subspaces.
*)

(* TODO *)

Section vector_line.

(**
The vector-line directed by $$u \in E$$ is $$\{ \lambda u \mid \lamdba \in \mathbb{K} \}$$.
(It is a subset of [E]).
*)

Definition vector_line (u : E)(x : E) := exists (l : K), x [=] (l [x] u).

Variable u:E.
Let lineProp := vector_line u.
Let line := sig lineProp.

(**
A vector-line is always a sub-vector-space of [E].
*)

Instance line_plus_closed : ClosedOp E lineProp plus.
    (*repeat red. intros.
    destruct x ; unfold lineProp in l ; unfold vector_line in l ; destruct l.
    destruct y ; unfold lineProp in l ; unfold vector_line in l ; destruct l.
    exists (x0 [+] x2).
    (* TODO *) *)
Admitted.
Instance line_plus : Plus line := Fplus E lineProp.

Lemma zero_in_line : lineProp Ezero.
Proof.
    (* TODO *)
Admitted.
Instance line_zero : Zero line := Fzero E lineProp zero_in_line.

Instance line_scalar_mult : ScalarMult K line.
    (* TODO : restriction of EScalarMult *)
Admitted.

Instance vector_line_svs : VectorSubspace lineProp.
    (* TODO *)
Admitted.

End vector_line.

Variable Fprop Gprop : E -> Prop.
Let F := sig Fprop.
Let G := sig Gprop.

(**
The intersection of two sub-vector-space is still a sub-vector-space of [E].
*)

Section svs_inter.

Definition svs_inter_prop := inter _ Fprop Gprop.
Let svs_inter := sig svs_inter_prop.

Instance svs_inter_closed : ClosedOp E svs_inter_prop plus.
    (* TODO *)
Admitted.
Instance svs_inter_plus : Plus svs_inter := Fplus E svs_inter_prop.

Lemma zero_in_svs_inter : svs_inter_prop Ezero.
Proof.
    (* TODO *)
Admitted.
Instance svs_inter_zero : Zero svs_inter := Fzero E svs_inter_prop zero_in_svs_inter.

Instance svs_inter_scalar_mult : ScalarMult K svs_inter.
    (* TODO *)
Admitted.

Instance svs_inter_svs : VectorSubspace svs_inter_prop.
    (* TODO *)
Admitted.

End svs_inter.

(**
The sum of two sub-vector-spaces [F] and [G] is :
$$F + G = \{x + y \mid x \in F \land y \in G \}$$.
*)

Section svs_sum.

Definition svs_sum_prop := fun z => exists (x y : E)(Hx : Fprop x)(Hy : Fprop y), z [=] (x [+] y).
Let svs_sum := sig svs_sum_prop.

Instance svs_sum_closed : ClosedOp E svs_sum_prop plus.
    (* TODO *)
Admitted.
Instance svs_sum_plus : Plus svs_sum := Fplus E svs_sum_prop.

Lemma zero_in_svs_sum : svs_sum_prop Ezero.
Proof.
    (* TODO *)
Admitted.
Instance svs_sum_zero : Zero svs_sum := Fzero E svs_sum_prop zero_in_svs_sum.

Instance svs_sum_scalar_mult : ScalarMult K svs_sum.
    (* TODO *)
Admitted.

Instance svs_sum_svs : VectorSubspace svs_sum_prop.
    (* TODO *)
Admitted.

(**
$$F + G$$ is the smallest vector subspace of [E] containing $$F \cup G$$ :
- $$F + G$$ is a sub-vector-space of [E] (Already proved)
- $$F \cup G \subset F + G$$
- If $$H$$ is a sub-vector space of [E] such that $$F \cup G \subset H$$, then $$F + G \subset H$$.
*)

Definition svs_union_prop := union _ Fprop Gprop.
Let svs_union := sig svs_union_prop.

Lemma svs_union_subset_sum : subset _ svs_union_prop svs_sum_prop.
Proof.
    (* TODO *)
Admitted.

Variable Hprop:E->Prop.
Context `{Hsvs : VectorSubspace Hprop}.

Lemma svs_union_smallest_subset : subset _ svs_union_prop Hprop 
    -> subset _ svs_sum_prop Hprop.
Proof.
    (* TODO *)
Admitted.

(**
The sum is direct if 
$$\forall w \in E, \exists ! (u, v) \in F \times G, w = u + v$$.
We then note $$F \oplus G$$ instead of $$F + G$$.
*)

Definition svs_direct_sum := forall (w : E), exists ! (x y : E)
    (Hx : Fprop x)(Hy : Fprop y), w [=] (x [+] y).

(**
$$F$$ and $$G$$ are direct sum if and only if $$F \cap G = \{0\}$$.
*)

Theorem svs_direct_sum_charac : iff (svs_direct_sum) (forall (x:E), svs_sum_prop x
    -> x [=] Ezero).
Proof.
     (* TODO *)
Admitted.

End svs_sum.

Section vector_plane.

(**
We define a vector plan as the direct sum of two vector line : 
*)

Definition vector_plane_prop (H : svs_direct_sum)(x : E) := svs_sum_prop x.

End vector_plane.

Section additional_svs.

(**
[F] and [G] are additional if : $$F \oplus G = E$$.
(The inclusion $$F \oplus G \subset E$$ is obvious, we only specify $$E \subset F \oplus G$$).
*)

Definition svs_additional := svs_direct_sum /\ (forall (x:E), svs_sum_prop x).

(**
[F] and [G] are additional in [E] if and only if 
$$\forall v \in E, \exists !(f, g) \in F \times G, v = f+g$$.
*)

Theorem svs_additional_charac : iff (svs_additional) (forall (v:E), exists! (f g : E),
    Fprop f -> Gprop g -> v [=] (f [+] g)).
Proof.
    (* TODO *)
Admitted.

End additional_svs.

End vector_definitions.

(**
* Subset of a vector-space
*)

