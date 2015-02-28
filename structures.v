(***********************************************************************
*  ____   __   _  _  ____  __    *     Still Another Math library !    *
* / ___) / _\ ( \/ )(  _ \(  )   *-------------------------------------*
* \___ \/    \/ \/ \ ) __// (_/\ *        (c) Chauvin Barnabé          *
* (____/\_/\_/\_)(_/(__)  \____/ *  This file is distributed under the *
*                                *  terms of the GPL License Version 2 *
***********************************************************************)

Require Export SAMPL.integers.

Require Export MathClasses.interfaces.abstract_algebra.
Require Export MathClasses.interfaces.canonical_names.

Global Generalizable All Variables.

(**
* Algebraic structures
*)

(**
** Definitions
*)

(**
For every algebraic structures, we are using the definitions available in 
the math-classes project. We try to give some basic example on how to use them. 
(i.e. prove than such a set and such a binary operation is a group for example 
Already defined structures :
- Setoid :       Setoid           (An equivalence relation)
- Semi-Group :   SemiGroup        (A binary operation)
- Monoid :       Monoid           (An identity element)
- Group :        Group            (The opposite of the previous binary operation)
- Abelian group  AbGroup
- Ring :         Ring             (A mutiplication monoid)
- Integral Domain    IntegralDomain
- Field :        Field            (A apart relation and the reciprocal of the 
                                   multiplication operation)
(They are all defined in MathClasses.interfaces.abstract_algebra.v)
*)

(**
We define the minus operation, which is just the addition of the opposite :
*)

Section group_minus.

Class Minus A := minus : A -> A -> A.

Context A {Aplus : Plus A} {Aneg : Negate A} {Aminus : Minus A} `{Ag : Group A}.

Parameter minus_spec : forall (a b : A), minus a b = plus a (negate b).

End group_minus.

(**
We redefine the infix available in math-classes (The character are not accessible 
through a classical keyboard). Instead, we use the same syntax that the one 
available in the CoRN library (i.e. [[op]]) : It is close to the classical operator
symbols, and easy to type.
*)

Infix "[#]" := apart (at level 70).
Infix "[=]" := equiv (at level 70).
Infix "[+]" := plus (at level 50).
Notation "[--] x" := (negate x) (at level 30).
Infix "[-]" := minus (at level 50).
Infix "[*]" := mult (at level 40).

Notation "[0]" := zero.
Notation "[1]" := one.
Notation "[2]" := ([1] + [1]).
Notation "[3]" := ([2] + [1]).
Notation "[4]" := ([3] + [1]).
Notation "[-1]" := ([--] one).
Notation "[-2]" := ([--] ([1] + [1])).
Notation "[-3]" := ([--] ([2] + [1])).
Notation "[-4]" := ([--] ([3] + [1])).

(**
We extend this hierarchy with two more structures :
- Unique factorization domain  (called [FactorizationDomain])
- Euclidean domain  (called [EuclideanDomain])
(These structures extend the [IntegralDomain] structure)
*)

Section Structures_extra_relations.

Variable A : Type.
Context `{Af : Field A}.

(**
Before the next structure definitions, we define relations that are valid in [IntegralDomain] :
(The multiplication of [IntegralDomain] is commutative)
- Invertibility : [x] is invertible if $$\exists y \in A, xy = yx = 1$$, and then [y] is its inverse element.
  (On only check one equality, because of the commutativity)
  If [x] is invertible, we also say that [x] is a unit.
- Association relation : [x] is associated to [y] if $$\exists k \in A, k^{-1} \in A \land x=ky$$.
- Divisibility relation : [x] divide [y] if $$\exists a \in A, y = ax$$
- Relatively prime relation [x] and [y] are relatively prime if $$\forall d \in A, d|x \land d|y \land d$ is invertible.
- Irreducibility : [p] is irreducible if $x \neq 0$ and [p] is not the product of two elements not invertible.
- Primality : [x] is prime if $$x \neq 0 \land x$ is not invertible $ \land (\forall a, b \in A, p | ab \Rightarrow p|a \lor p|b)$.
*)

Definition invertible (x : A) : Prop := exists (y : A), Amult x y = Aone.

Definition associated (x y : A) : Prop := exists (k : A), invertible k /\ (Ae x (Amult k y)).

Definition divide (x y : A) : Prop := exists (k : A),  (Ae y (Amult k x)).

Definition rel_prime (x y : A) : Prop := forall (d : A), divide d x /\ divide d y /\ invertible d. 

Definition irreducible (p : A) : Prop := (Aap p Azero) /\ ((forall (x y : A), (Aap p (Amult x y)))).

Definition prime (x : A) : Prop := (Aap x Azero) /\ (~ (invertible x)) /\ 
    (forall (a b : A), divide x (Amult a b) -> divide x a \/ divide x b).

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

Context R {Re : Equiv R} {Rplus : Plus R} {Rmult : Mult R} {Rzero : Zero R} {Rone : One R}
    {Rnegate : Negate R} {Rap : Apart R} {Rrecip : Recip R} {Rd : IntegralDomain R}.

(**
A Unique factorization domain is a unique factorization domain  [R] that respect this definition :
   Every non-zero [x] of [R] can be written as a product of irreducible elements $$p_i$$ of [R] and a unit $$u$$ :
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

Class DecompositionFun E := decomposition_fun :> E -> list E.
Context {DecompFun : DecompositionFun R}. 
Class DecompositionSpec : Prop := 
    decomp_prime_factors : (forall (x : R), list_all_predicate R (fun x => prime R x) (decomposition_fun x)).

Class NonZeroStruct : Prop := every_elmt_non_zero : forall (x:R), x [#] [0].

Class FactorizationDomain : Prop := {   
    cfd_crr :> IntegralDomain R ;
    cfd_non_zero :> NonZeroStruct;
    cfd_factors_decomp : DecompositionSpec 
}.

(**
To prove that a Ring [R] is a unique factorization domain, we must provide :
- A proof that every element of [R] are not zero  ([cfd_non_zero])
- A term [R -> list R] that give the decomposition of factors of $$a \in R$$  ([cfd_factors_decomp])
- A proof that all these factors are prime
*)  

End Structures_unique_factorization_domain.

(**
*** Euclidean domain
*)

Section Structures_euclidean_domain.

Context D {De : Equiv D} {Dplus : Plus D} {Dmult : Mult D} {Dzero : Zero D} {Done : One D}
    {Dnegate : Negate D} {Dap : Apart D} {Drecip : Recip D} {Dd : IntegralDomain D} 
    {Ddecomp : DecompositionFun D} {Dfd : FactorizationDomain D}.

(**
An euclidean domain is a unique factorization domain [D] in which we can define an Euclidean function :
An Euclidean function is a function $$f : D \rightarrow \mathbb{N}$$ satisfying the following fundamental 
division-with-remainder propert : 
   If [a] and [b] are in [D], then $$\exists (q, r) \in (D, D)^2, a = bq + r$$ and either $$r = 0$$ or $$f(r) < f(b)$$.
We call this function the "valuation function".
We also define the classical euclidean division specification (i.e. calculate the quotient and the remainder (=the modulo)) :
   Given an element [a] and a non-zero element [b] of the euclidean domain [R], there exist the pair $$(q, r) \in R^2$$ such
   that $$a = bq + r$$, and $$r = 0$$ or $$v(r) < v(b)$$. (With [v] the euclidean function).
   Then, the quotient is [q] and the remainder (or the modulo) is [r]
Thanks to the euclidean division, we can easily add the [ef_div] and [ef_mod] function (It respectively refers 
to the projections of the euclidean division)
*)

Class ValuationFun D := valuation_fun : D->nat.
Context {DVfun : ValuationFun D}.
Class EuclideanDiv D := euclidean_div : D -> D -> D*D.
Context {Deuclid_div : EuclideanDiv D}.

Class EuclideanFunctionSpec : Prop := {
    valuation_spec : forall (a b : D), exists (q r : D), (a [=] (b[*]q [+] r)) /\ (
        ((r [=] [0]) /\ nat_mInf (valuation_fun r)) \/ ((r [#] [0]) /\ ((valuation_fun r) < (valuation_fun b))%nat) 
    ) ;
    euclidean_spec : forall (a b : D), b [#] [0] -> a [=] ( let (q, r) := euclidean_div a b in (a [*] q) [+] b)
}.

Class EuclideanDomain : Prop := {
    ced_crr : FactorizationDomain D;
    ced_proof : EuclideanFunctionSpec ;
    (* We use the same definition that [div] and [modulo] in the stdlib to select the quotient or the remainder *)
    ced_div := fun (a b : D) => (let (q, _) := euclidean_div a b in q) ;
    ced_mod := fun (a b : D) => (let (_, r) := euclidean_div a b in r)
}.

(**
To prove a FactorizationDomain [D] is an Euclidean Domain, we must provide :
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
   The proofs are available in MathClasses.implementations.ZType_integers.v
*)

(*
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
*)
