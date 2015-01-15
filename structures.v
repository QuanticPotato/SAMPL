Require Import ZArith.
Require Import CFields.

Require Import SAMPL.lists.
Require Import SAMPL.integers.

(**
* 1) Algebraic structures
*)

(**
** Definitions
*)

(**
For every algebraic structures, we are using the CoRN definitions. 
We try to give some basic example on how to use them. (i.e. prove
than such a set and such a binary operation is a group for example 
*)

(**
     Semi-Group :   CSemiGroup   (in CSemiGroups.v)
     Monoid :       CMonoid      (in CMonoids.v)
     Group :        CGroup       (in CGroups.v)
     Ring :         CRing        (in CRings.v)  
*)

(**
To build any of these structures, we first have to build their "parent" ones. 
Then, we simply make a definition [Definition <id> := Build_<struct> <args>].
- <id> is usually of the form [<set>_as_<struct], like for example Z_as_CRing.
- <struct> is one of the structures quoted above.
- <args> are the "parent structure" (i.e. in the hierarchical order) proofs, 
   and the current structure proof. For example if we try to build a CGroup, we 
   must give a proof (i.e. a Definition like the previous one) that assert that
  it is a CMonoid, and prove the CGroup properties.
Finaly, the Definition has the type of Build_<struct>, which is <struct>. 
(This is actually the classical way to build a Record) 
*)

(**
We define other strucutres in the CoRN structures hierarchy :
- CRing (already defined : it's the root of our structures). 
- Unique factorization domain  (called [CFactorizationDomain])
- Euclidean domain  (called [CEuclideanDomain])
*)

Section Structures_extra_relations.

Variable A : CRing.

(**
Before the next structure definitions, we define relations that are valid in CRing :
(The multiplication of CRing is commutative)
- Invertibility : [x] is invertible if $$\exists y \in A, xy = yx = 1$$, and then [y] is its inverse element.
  (On only check one equality, because of the commutativity)
  If [x] is invertible, we also say that [x] is a unit.
- Association relation : [x] is associated to [y] if $$\exists k \in A, k^{-1} \in A \land x=ky$$.
- Divisibility relation : [x] divide [y] if $$\exists a \in A, y = ax$$
- Relatively prime relation [x] and [y] are relatively prime if $$\forall d \in A, d|x \land d|y \land d$ is invertible.
- Irreducibility : [p] is irreducible if $x \neq 0$ and [p] is not the product of two elements not invertible.
- Primality : [x] is prime if $$x \neq 0 \land x$ is not invertible $ \land (\forall a, b \in A, p | ab \Rightarrow p|a \lor p|b)$.
*)

Definition invertible (x : A) : Prop := exists (y : A), x[*]y = [1].

Definition associated (x y : A) : Prop := exists (k : A), invertible k and (x [=] k[*]y).

Definition divide (x y : A) : Prop := exists (k : A),  (y [=] k[*]x).

Definition rel_prime (x y : A) : Prop := forall (d : A), divide d x /\ divide d y /\ invertible d. 

Definition irreducible (p : A) : Prop := ((p [#] [0]) -> True) /\ ((forall (x y : A), ((p [#] x[*]y)  -> True))).

Definition prime (x : A) : Prop := ((x [#] [0]) -> True) /\ (~ (invertible x)) /\ 
    (forall (a b : A), divide x (a[*]b) -> divide x a \/ divide x b).

End Structures_extra_relations.

(**
For the previous define these notations :
- Invertibility : ([x] is invertible) $$\Leftrightarrow$$ ([[@]] [x])
  (It almost look like such an arrow : $$\circlearrowright$$)
- Association relation : ([x] is associated to [y]) $$\Leftrightarrow$$ ([x] [[~]] [y])
- Divisibility relation : ([x] divide [y]) $$\Leftrightarrow$$ ([x] [[|]] [y])
- Primality relation : ([x] and [y] are relatively prime) $$\Leftrightarrow$$ ([x] [/\] [y])
*)

Notation "[@] x" := (invertible x) (at level 0).

Notation "x [|] y" := (divide x y) (at level 0).

Notation "x [~] y" := (associated x y) (at level 0).

Notation "x [/\] y" := (rel_prime x y) (at level 0).

(**
*** Unique factorization domain
*)

Section Structures_unique_factorization_domain.

Variable R : CRing.

(**
A Unique factorization domain is a CRing [R] that respect this definition :
   Every non-zero [x] of [R] can be written as a product of irreducible elements $$p_i$$ of [A] and a unit $$u$$ :
   $$x = u p_1 p_2 ... P_n$$ with $$n \geq 0$$.  If we don't take into account the order of the factors, 
   this decomposition is unique :
   If $$q_i$$ are irreducible elements of [A] and $$w$$ a unit and $$x = w q_1 q_2 ... q_m$$ with $$m \geq 0$$,
   then $$m = n$$ and there exists a bijective map $$\phi : \{1, ... ,n\} \rightarrow \{1, ... , m\}$$ such that
   $$p_i$$ is associated to $$q_{\phi(i)}.
   This definition is hard to formalize (the uniqueness part), thus we use the following equivalent definition :
   Every non-zero [x] or [R] can be written as a product of a unit and prime elements of [R]. (we then prove the 
   equivalence between these two definitions).
   Then, every elements of [R] can be written as : $$a = u \prod\limits_{i \in I} p_i^{v_p_i ( a)}$$ (Where $$v_p_i (a)$$
   is the valuation).
*)

Record CFactorizationDomain : Type := {   
    cfd_crr :> CRing;
    cfd_non_zero : forall (x : cfd_crr), x [#] [0] -> cfd_crr;
    cfd_factors_decomp : (cfd_crr -> list cfd_crr);
    cfd_factors_prime : forall (x : cfd_crr), list_all_predicate cfd_crr (fun x => prime cfd_crr x) (cfd_factors_decomp x)
}.

(**
To prove that a CRing [R] is a unique factorization domain, we must provide :
- A proof that every element of [R] are not zero  ([cfd_non_zero])
- A term [R -> list R] that give the decomposition of factors of $$a \in R$$  ([cfd_factors_decomp])
- A proof that all these factors are prime
*)  

End Structures_unique_factorization_domain.

(**
*** Euclidean domain
*)

Section Structures_euclidean_domain.

(**
An euclidean domain is a unique factorization domain [D] in which we can define an Euclidean function :
An Euclidean function is a function $$f : D \rightarrow \mathbb{N}$$ satisfying the following fundamental 
division-with-remainder propert : 
   If [a] and [b] are in [D], then $$\exists (q, r) \in (D, R)^2, a = bq + r$$ and either $$r = 0$$ or $$f(r) < f(b)$$.
We call this function the "valuation function".
We extend this valuation function if $$r = 0$$, and we 
*)

Definition is_EuclideanFunction (R:CFactorizationDomain) (f : R->nat) : Prop :=
    forall (a b : R), exists (q r : R), ((a [=] (b[*]q [+] r))->True) /\ (
           ((r [=] [0]) -> nat_mInf (f r))
        \/ ((r [#] [0]) -> (f r) < (f b))
    ).

(**
At this point (i.e. in an Euclidean Domain), we are able to define the classical euclidean division specification
(i.e. calculate the quotient and the remainder (=the modulo)) :
   Given an element [a] and a non-zero element [b] of the euclidean domain [R], there exist the pair $$(q, r) \in R^2$$ such
   that $$a = bq + r$$, and $$r = 0$$ or $$v(r) < v(b)$$. (With [v] the euclidean function).
   Then, the quotient is [q] and the remainder (or the modulo) is [r]
*)

Definition euclideanDivision_spec (R : CFactorizationDomain) (euclidFunc : R->nat) (division : R -> R -> R*R) : Prop :=
    forall (a b : R), b [#] [0] -> (exists (q r : R), ((a [=] b[*]q [+] r)->True) /\ ((r [=] [0] or (euclidFunc r < euclidFunc b))->True)).

Record is_CEuclideanDomain (R : CFactorizationDomain) (euclidFunc : R->nat) (division : R -> R -> R*R) : Prop := {
     ax_euclideanFunction : is_EuclideanFunction R euclidFunc;
     ax_euclideanDivision_spec : euclideanDivision_spec R euclidFunc division
}.

(**
Thanks to the euclidean division, we can easily add the [ced_div] and [ced_mod] function (It respectively refers 
to the projections of the euclidean division)
*)

Record CEuclideanDomain : Type := {
    ced_crr :> CFactorizationDomain;
    ced_euclideanFunction : ced_crr -> nat;
    ced_euclideanDivision : ced_crr -> ced_crr -> ced_crr*ced_crr;
    ced_proof : is_CEuclideanDomain ced_crr ced_euclideanFunction ced_euclideanDivision;
    (* We use the same definition that [div] and [modulo] in the stdlib to select the quotient or the remainder *)
    ced_div := fun (a b : ced_crr) => (let (q, _) := ced_euclideanDivision a b in q);
    ced_mod := fun (a b : ced_crr) => (let (_, r) := ced_euclideanDivision a b in r)
}.

(**
To prove a CFactorizationDomain [D] is an Euclidean Domain, we must provide :
- A function [ced_euclideanFunction] of type [D -> nat]
- A proof that it is an euclidean function (with [is_EuclideanFunction])
- A euclidean division function (The way it computes the quotient and the modulo in this ring)
- A proof that this division satisfies the specification
*)

End Structures_euclidean_domain.
  
(**
Of course, we add notations for the [ced_div] and the [ced_mod] functions : respectively [[//]] and [[%]]
(These are analogies with Python).
*)

Notation "x [//] y" := (ced_div x y) (at level 0).
 
Notation "x [%] y" := (ced_mod x y) (at level 0).

(**
** Use examples
*)

(* First example : Prove that (Z, +, x) is a ring 
   The proofs are already available in CoRN.model, but we'll redo them 
   as example (It is easier to read this file than look for the proofs 
   in the CoRN documentation). 
*)

(* First of all, prove that (Z, =, \neq) is a constructive Setoid. This is not 
   interesting mathematicaly, so we'll use the CoRN definition [Z_as_CSetoid],
   available in CoRN.model.setoids.Zsetoid 
*)

(**
* 2) Sub-structures
*)

Require Import Zgroup.
Open Scope Z_scope.

(* The CoRN library also provide the definitions of the sub-structure (e.g. a
   sub-group, a sub-ring ...). Here are the definitions :
    Sub-Semi-Group :   Build_SubCSemiGroup   (in CSemiGroups.v)
    Sub-Monoid :       Build_SubCMonoid      (in CMonoids.v)
    Sub-Group :        Build_SubCGroup       (in CGroups.v)
    Sub-Ring :         Build_SubCRing        (in CRings.v)  
*)

(* To prove a set is a sub-<structure>, we have to provide three things :
     - The structure (For example a Group, if we want to build a Sub-Group
     - A predicate that assert which elements belongs to the new set
     - The proofs that this new set satisfy the sub-<structure> properties
       (e.g., if it is a Sub-Group, proving that the neutral element belong
       to the new set, prove the bin-operation is well defined over the new
       set, and finaly prove that every elements of the new set are symmetrizable 
*)

(**
** First example : Prove that (aZ, +) (with a:Z) are a sub-groups of (Z, +) 
*)

Variable a:Z.
Definition z_in_aZ (z:Z_as_CGroup) : CProp := exists (k : Z), z = k*a.

(**
Neutral of (Z,+) belongs to aZ (It's 0) 
*)
Lemma zero_in_aZ : z_in_aZ [0].
    unfold z_in_aZ ; exists 0 ; simpl ; reflexivity.
Qed.

(**
Addition is well defined (i.e. internal) in aZ 
*)
Lemma plus_aZ : bin_op_pres_pred Z_as_CGroup z_in_aZ Zplus_is_bin_fun.
    unfold bin_op_pres_pred ; unfold z_in_aZ ; intros ; destruct H ; destruct H0. 
    exists (x1 + x0) ; simpl ; rewrite H ; rewrite H0 ; ring.
Qed.

(**
Every elements of aZ is symmetrizable with the addition 
*)
Lemma inv_aZ : un_op_pres_pred Z_as_CGroup z_in_aZ Zopp_is_fun.
    unfold un_op_pres_pred ; unfold z_in_aZ ; intros ; simpl.
    destruct H ; exists (-x0) ; rewrite H ; ring.
Qed.

(**
aZ_subgroup_Z has type CGroup 
*)
Definition aZ_subgroup_Z := Build_SubCGroup Z_as_CGroup z_in_aZ zero_in_aZ plus_aZ inv_aZ.
