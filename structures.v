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
- Setoid :       [Setoid]           (An equivalence relation)
- Semi-Group :   [SemiGroup]        (A binary operation)
- Monoid :       [Monoid]           (An identity element)
- Group :        [Group]            (The opposite of the previous binary operation)
- Abelian group  [AbGroup]
- Ring :         [Ring]             (A mutiplication monoid)
- Integral Domain    [IntegralDomain]
- Field :        [Field]            (A apart relation and the reciprocal of the 
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
Notation "[-1] x" := (recip x) (at level 20).

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
We define a few rewriting lemmas and tactics :
*)

Section rewriting_lemmas.

Context E {Ee : Equiv E} {Eequiv_refl : Reflexive Ee}{Eequiv_symm : Symmetric Ee}.

(**
Sometime, it might be useful to convert our structure equality ([equiv]) to the coq leibniz equality ([eq]),
in order to use stdlib lemmas for example :
*)

Lemma eq_comp : forall (x y : E), eq x y -> x[=]y.
Proof.
    intros. now rewrite H.
Qed.

(**
We also add a characterization of the MathClasses [Associative] property, in order to provide a fast access to
the mathematical definition (i.e. get rid of [HeteroAssociative]) :
*)
Lemma assoc_charac `(Associative E R) : forall (x y z : E), ((R x (R y z))) [=] ((R (R x y)) z) .
Proof.
    auto.
Qed.

(**
If [E] is a group, it might be usefull to rewrite an equality (in an hypothesis) of members of this group, with 
the same equality multiplied (i.e. applied with the group [SgOp]) with an operand (of type E).
For example, if we have the hypothesis [H : x [=] y], the call [group_op H z] will rewrite [H] to [H : x[*]z [=] y[*]z]
(assuming [z] is of type [E]).
! The [SgOp] operation must be proper !
*)

End rewriting_lemmas.

Ltac group_op H operand op :=
  let Htmp := fresh in 
    unfold equiv in H ; (* If we don't unfold, the match fail .. *)
    match type of H with
        | ?rel ?v1 ?v2 => (* Analyse the relation type (to retrieve the group type) *)
            match type of rel with 
                | Equiv ?E => 
                match type of operand with 
                    | E => 
                        (* We simply rewrite with the original lemma, and then prove by reflexivity *)
                        assert ((op v1 operand) [=] (op v2 operand)) as Htmp ; [(rewrite H ; reflexivity) | idtac] ;
                        (* Then we rename the new hypothesis *)
                        clear H ; rename Htmp into H
                    | _ => idtac "The operand must belong to the group !" ; fail
                    end
                | _ => idtac "Not the expected group equality !" ; fail
            end
        | _ => idtac "Not the expected group equality !" ; fail
    end.

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
- Relatively prime relation [x] and [y] are relatively prime if $$\forall d \in A, d|x \land d|y \land d$$ is invertible.
- Irreducibility : [p] is irreducible if $$x \neq 0$$ and [p] is not the product of two elements not invertible.
- Primality : [x] is prime if $$x \neq 0 \land x$$ is not invertible $$\land (\forall a, b \in A, p | ab \Rightarrow p|a \lor p|b)$$.
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
   $$p_i$$ is associated to $$q_{\phi(i)}$$.
   This definition is hard to formalize (the uniqueness part), thus we use the following equivalent definition :
   Every non-zero [x] or [R] can be written as a product of a unit and prime elements of [R]. (we then prove the 
   equivalence between these two definitions).
   Then, every elements of [R] can be written as : $$a = u \prod\limits_{i \in I} p_i^{v_{p_i} ( a)}$$ (Where $$v_{p_i} (a)$$
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

(**
First example : Prove that (Z, +, x) is a ring.
The proofs are available in MathClasses.implementations.ZType_integers.v
*)

(**
* Sub-structures
In this section, we define the algebraic sub-structures : A sub-field, a sub-ring .. 

These sub-structures are subsets of their "root-structures", that satisfy several axioms.
The subsets will be characterized by a predicate [E->Prop] (that assert which elements 
belongs to the subset), and a sigma type [F].
*)

Section Substructures_definition.

Variable E:Set.
Variable Fprop : E->Prop.
Let F:= sig Fprop.
Let inj := sig_injection E Fprop.

(**
$$F$$ is closed under the operation $$\cdot$$ if $$\forall x, y \in F, x \cdot y \in F$$.
*)

Class ClosedOp (op : E->E->E) : Prop := closed_internal_op : forall (x y : F), Fprop (op (inj x) (inj y)).

Instance PropEquiv : Equiv Prop.
    refine (fun (x y : Prop) => eq x y).
Defined.

(**
** Equivalence relations
We define the restriction for the equivalence relation. (Every structure need this relation)
(We also easily prove the three properties of the relation : reflexivity, symmetry, transitiviy)
*)

Context {Ee : Equiv E} {Eequiv_refl : Reflexive Ee} {Eequiv_symm : Symmetric Ee} 
    {Eequiv_trans : Transitive Ee}.

Instance Fe : Equiv F.
    red ; refine (fun (x y : F) => (inj x) [=] (inj y)).
Defined.

Instance Fequiv_refl : Reflexive equiv.
    red ; intros ; apply Eequiv_refl.
Defined.

Instance Fequiv_symm : Symmetric equiv.
    red ; intros ; apply Eequiv_symm in H ; apply Eequiv_symm ; now apply Eequiv_symm in H. 
Defined.

Instance Fequiv_trans : Transitive equiv.
    (* Unfold and reduce *)
    red ; intros. repeat unfold equiv,Fe in H, H0. repeat unfold equiv, Fe.
    now apply Eequiv_trans with (y:=(inj y)).
Defined.

Lemma inj_ext_eq : forall (x y : F), Fe x y -> Ee (inj x) (inj y).
Proof.
    intros. unfold Fe in H. assumption.
Qed.

(**
We can rewrite under our injection [inj], and under the [exist] constructor (the reciprocal of the
injection [inj]).
*)

Instance Ee_inj_proper : Proper (Fe ==> Ee) inj.
    auto.
Defined.

(** TODO !! *)

Instance Ee_fprop_proper : Proper (Ee ==> iff) Fprop.
    repeat red. intros. split ; intro.
Admitted.

Lemma exist_eq : forall (x y : E)(Hx : Fprop x)(Hy : Fprop y), x[=]y -> 
    (exist Fprop x Hx) = (exist Fprop y Hy).
Proof.
Admitted.

(**
The tactic [rewrite_exist] allow to rewrite [x:E] under a [exist Fprop x Hx] 
statement (where [Hx] is a proof of [Fprop x]).
*)

Ltac rewrite_exist lemma :=
    match type of lemma with 
        | equiv ?v1 ?v2 => 
            match goal with
                | [ Hprop : Fprop v1 |- _ ] => let H2 := fresh in
                    match type of Hprop with
                        | ?P => (* Duplicate H : *) assert P as H2 by auto ;
                            rewrite lemma in H2 ;rewrite (exist_eq v1 v2 Hprop H2 lemma)
                    end
                | _ => idtac "fail 2"
            end 
        | _ => idtac "fail 1"
    end.

(**
** Sub-group
The group structure provides an addition (And its opposite) and a unit.
We moreover assume that $$F$$ is closed under this addition (When one define an instance
of any of the following substructures, it will have to prove that the addition is closed).
*)

Context {Eplus : Plus E} {Eplus_assoc : Associative Eplus} 
    {Ezero : Zero E} {Ezero_left : LeftIdentity Eplus Ezero}
    {Ezero_right : RightIdentity Eplus Ezero} {Enegate : Negate E} 
    {Enegate_proper : Proper (respectful Ee Ee) Enegate} {Eg : Group E}
    {Eplus_proper : Proper (Ee ==> Ee ==> Ee) plus}.
Context {PlusClosed : ClosedOp plus}.

Section subgroup_def.

(**
The addition in $$F$$ is just the restriction of the addition in $$E : +F = {+E}_{|F \times F}$$.
(As for [Equiv], we then prove this operation is [Associative] and [Proper])
*)

Global Instance Fplus : Plus F .
    unfold Plus ; refine (fun (x y : F) => exist Fprop ((inj x) [+] (inj y)) _ ).
    apply closed_internal_op.
Defined.

Global Instance Fplus_assoc : Associative Fplus.
    repeat red ; unfold Fplus ; intros ; apply Eplus_assoc.
Defined.

Lemma inj_ext_eplus : forall (x y:F), Eplus (inj x) (inj y) [=] inj (Fplus x y).
Proof.
    intros ; unfold Fplus ; pose (X:=(inj x[+]inj y)) ; pose (H:=(closed_internal_op x y)).
    assert ((inj (exist Fprop X H)) [=] X). apply sig_simpl ; auto. 
    assumption.
Qed.

Global Instance Fplus_proper : Proper (Fe ==> Fe ==> Fe) Fplus.
    (* Unfold the definition *)
    repeat red ; intros.
    (* We can prove easily than $$x +E x_0 =E y +E y_0$$ *)
    assert (plus (inj x) (inj x0) = plus (inj y) (inj y0)) by (rewrite H, H0 ; reflexivity).
    (* Then, we use [sig_simpl] *)
    assert ((inj (exist _ (_ (_ x) (_ x0)) (closed_internal_op x x0))) [=] 
        (plus (inj x) (inj x0))) by exact (sig_simpl _ _ _ _ _).
    assert ((inj (exist _ (_ (_ y) (_ y0)) (closed_internal_op y y0))) [=] 
        (plus (inj y) (inj y0))) by exact (sig_simpl _ _ _ _ _).
    now rewrite H2, H3.
Defined.

Lemma inj_ext_fplus : forall (x y : F), inj (Fplus x y) [=] Eplus (inj x) (inj y).
Proof.
    intros ; rewrite inj_ext_eplus ; auto.
Qed.

(**
We can now define the Sub-group itself.
*)

Context {Fzero : Zero F} {Fnegate : Negate F}.

Class SubGroup : Prop := {
    subg_axioms :> Group F
}.

End subgroup_def.

(**
** Sub-ring
*)

Context {Eplus_comm : Commutative Eplus} {Emult : Mult E} {Emult_assoc : Associative Emult} 
    {Emult_comm : Commutative Emult} {Eone : One E} {Edistr : LeftDistribute Emult Eplus}.
Context {MultClosed : ClosedOp Emult} {Emult_proper : Proper (Ee ==> Ee ==> Ee) mult}.

Section subring_def.

Global Instance Fmult : Mult F .
    unfold Mult ; refine (fun (x y : F) => exist Fprop ((inj x) [*] (inj y)) _ ).
    apply closed_internal_op.
Defined.

Global Instance Fmult_assoc : Associative Fmult.
    repeat red ; intros ; apply Emult_assoc.
Defined.

Global Instance Fplus_comm : Commutative Fplus.
    repeat red ; intros ; apply Eplus_comm.
Defined.

Global Instance Fmult_comm : Commutative Fmult.
    repeat red ; intros ; apply Emult_comm.
Defined.

Global Instance Fmult_proper : Proper (Fe ==> Fe ==> Fe) Fmult.
    (* Unfold the definition *)
    repeat red ; intros.
    (* We can prove easily than $$x \cdot x_0 =E y \cdot y_0$$ *)
    assert (mult (inj x) (inj x0) = mult (inj y) (inj y0)) by (rewrite H, H0 ; reflexivity).
    (* Then, we use [sig_simpl] *)
    assert ((inj (exist _ (_ (_ x) (_ x0)) (closed_internal_op x x0))) [=] 
        (mult (inj x) (inj x0))) by exact (sig_simpl _ _ _ _ _).
    assert ((inj (exist _ (_ (_ y) (_ y0)) (closed_internal_op y y0))) [=] 
        (mult (inj y) (inj y0))) by exact (sig_simpl _ _ _ _ _).
    now rewrite H2, H3.
Defined.

Global Instance Fdistr : LeftDistribute mult plus.
    repeat red ; intros ; apply Edistr.
Defined.

(**
We can now define the Sub-ring itself.
*)

Context {Fzero : Zero F} {Fnegate : Negate F} {Fone : One F}.

Class SubRing : Prop := {
    subr_axioms :> Ring F
}.

End subring_def.

(**
** Sub-field
The subset must be closed under the addition and the multplication (and their reciprocal). Hence,
it must contains 0 and 1.
*)

Context {Eap : Apart E} {Erecip : Recip E} {Ef : Field E}.

Section subfield_def.

(**
We define the restrictions for the subset [F] : 
*)

Global Instance Fapart : Apart F.
    unfold Apart, relation. refine (fun (x y : F) => (inj x) [#] (inj y)).
Defined.


(**
We first define an injection [ApartZero F -> ApartZero E] (using [inj]).
*)

Context {Hplus : ClosedOp plus}.
Context {Hmult : ClosedOp mult}.

Context {Fone : One F} {Fnegate : Negate F} {Fap : Apart F} {Fzero : Zero F} 
{Frecip : Recip F} {H : Field F}.

Class SubField : Prop := {
    subf_add_closed :> ClosedOp Eplus ;
    subf_mult_closed :> ClosedOp Emult ;
    subf_axioms :> Field F
}.

End subfield_def.

(**
** Substructures characterization
For all of our previously defined sub-structure, we define a "usefull characterization", that allows to prove 
a substructure with less axioms.
All these characterizations are composed of two implications (they are equivalences).
*)

Section Substructures_criteria.

Section first_implication.

(**
For the subgroups, we suppose that 
- H1 : $$0_E \in F$$, thus we can build our $$0_F$$.
- H2 : $$\forall x, y \in F, x + y \in F$$
- H3 : $$\forall x \in F, -x \in F$$. We can then define [Fnegate] as the restriction of [Enegate].
*)

Hypothesis Ezero_F : Fprop Ezero.
Instance Fzero : Zero F := (exist Fprop Ezero Ezero_F).

Hypothesis Fplus_closed : ClosedOp plus.

Hypothesis Fnegate_F : forall (x:F), Fprop ([--] (inj x)).
Instance Fnegate : Negate F.
    unfold Negate. refine (fun x => exist Fprop ([--] (inj x)) _). apply Fnegate_F.
Defined.

Lemma subgroup_criteria_1 : SubGroup.
Proof.
    assert ((inj (Ezero ↾ Ezero_F)) [=] Ezero) by exact (sig_simpl _ _ _ _ _).
    (* We already proved some axioms with our hypothesis *)
    repeat split ; auto. exact Fplus_assoc. exact Fplus_proper.
    (* [Fzero] is the left and right identity element : *)
    repeat red ; intros ; rewrite inj_ext_fplus ; rewrite H.
      rewrite left_identity ; reflexivity.
    repeat red ; intros ; rewrite inj_ext_fplus ; rewrite H.
      rewrite right_identity ; reflexivity.
    (* We easily prove [Fnegate] is proper because it is just a restriction of [Enegate] : *)
    repeat red ; intros ; unfold negate ; unfold Fnegate ; unfold negate.  
      assert ((inj (exist Fprop (Enegate (inj x))(Fnegate_F x)) [=] (Enegate (inj x)))) by exact (sig_simpl _ _ _ _ _).
      assert ((inj (exist Fprop (Enegate (inj y))(Fnegate_F y)) [=] (Enegate (inj y)))) by exact (sig_simpl _ _ _ _ _).
      rewrite H1, H2, H0. reflexivity.
    (* TODO *)
Admitted.

(**
For the subrings, we moreover suppose that : 
- H4 : $$1_E \in F$$ thus we can build our $$1_F$$.
- H5 : $$\forall x, y \in F, x \cdot y \in F$$
*)

Hypothesis Eone_F : Fprop Eone.
Global Instance Fone : One F := (exist Fprop Eone Eone_F).

Hypothesis Fmult_closed : ClosedOp mult.

Lemma subring_criteria_1 : SubRing.
Proof.
    (* We use the previous characterization .. *)
    split. split ; [split ; [ apply subgroup_criteria_1 |
    (* We already proved some properties (see previous instance) *)
    exact Fplus_comm] | idtac | exact Fdistr].
    (* $$(F, \cdot)$$ is a commutative monoid : *)
    (repeat split ; auto) ; [exact Fmult_assoc | exact Fmult_proper | idtac | idtac 
        | exact Fmult_comm].
      (* TODO ! *)
      admit. admit.
Qed.

(** 
For the subfields, we moreover suppose that :
- H6 : $$\forall x \in F, x \neq 0 \Rightarrow x^{-1} \in F$$
*)

Hypothesis Frecip_F : forall (x: ApartZero E), Fprop ([-1] x).
(*Instance Frecip : Recip F.
    unfold Recip.  refine (fun x => exist Fprop (Erecip x) _). apply Frecip_F.
Defined.*)

(*Lemma subfield_criteria_1 : SubField. 
Proof.
    (* TODO  ! *)
Admitted.*)

End first_implication.

(**
For the second implication, we suppose the witness is a substructure, and we prove that it satisfy the 
previously stated axioms (i.e. H1, H2 ...)
*)

Section second_implication.

(**
For the subgroups, we prove that $$1_E \in F$$, $$\forall x, y \in F, x + y \in F$$ (It is immediate with 
our defintion of the internal addition of [F]), $$\forall x \in F, -x \in F$$.
*)

Context `{Fg : SubGroup}.

Lemma subgroup_criteria_2 : Fprop Ezero /\ (forall (x : F), Fprop (Enegate (inj x))).
Proof.
    (* To prove that $$0_E \in F$$, we prove that $$0_E = 0_F$$ *)
        pose (f0:= inj Fzero0) ; pose (f0_opp := Enegate f0).
        (* First, we prove that $$0_F +_E 0_F = 0_F$$ *)
        assert (f0 [+] f0 = f0) ; unfold f0. rewrite inj_ext_eplus. rewrite left_identity. reflexivity.
        (* We prove that $$((-0_F) +_E 0_F) +_E 0_F = (-0_F) +_E 0_F = 0_E$$ and that 
              $$((-0_F) +_E 0_F) +_E 0_F = 0_F$$ *)
            assert (f0_opp [+] f0 [+] f0 [=] Ezero) by
                (rewrite <- assoc_charac ; auto ; rewrite H ; unfold f0_opp ;  now apply negate_l).
            assert (f0_opp [+] f0 [+] f0 [=] f0). assert (f0_opp[+]f0 [=] Ezero) by now apply negate_l.
              rewrite H1 ; rewrite left_identity ; reflexivity.
        (* Then, we prove that $$0_E = 0_F$$ by transitivity *)
        assert (Ezero [=] f0). transitivity (plus (plus f0_opp f0) f0) ; auto.
          split ; intros. rewrite H2 ; unfold f0, inj, sig_injection ; auto.
    (* Likewise $$0_E \in F$$, we prove $$\forall x \in F, -_Ex \in F$$ by proving that $$-_Ex = -_Fx$$ *)
        pose (xneg := Enegate (inj x)). pose (xneg' := inj (Fnegate0 x)).
        (* First, we prove that $$x -_F x = x -_E x$$ *)
        assert (xneg' [+] (inj x) [=] f0) by (unfold xneg, xneg', f0 ; rewrite inj_ext_eplus ;
            rewrite left_inverse; unfold mon_unit, zero_is_mon_unit ; reflexivity).
        assert (xneg [+] (inj x) [=] Ezero) by (unfold plus, xneg ; rewrite left_inverse ; 
            unfold mon_unit ; reflexivity).
        assert (xneg' [+] (inj x) [=] xneg [+] (inj x)). rewrite <- H2 in H3. transitivity Ezero ; auto.
        (* Then we just add $$-_Ex$$ on the right$$ : *)
        assert (xneg [=] xneg'). group_op H5 xneg Eplus. unfold equiv, plus in H5. 
          rewrite <- (assoc_charac E Eplus_assoc) in H5. unfold xneg in H5 ; rewrite left_inverse in H5 ;
          rewrite right_inverse in H5 ; unfold mon_unit, zero_is_mon_unit in H5 ;rewrite left_identity in H5 ;
          rewrite right_identity in H5 ; rewrite H5 ; reflexivity.
        unfold xneg in H6 ; rewrite H6 ; unfold xneg', inj, sig_injection ; auto.
Qed.

(**
For subrings, we prove that $$1_E \in F$$ thus we can build our $$1_F$$ and
$$\forall x, y \in F, x \cdot y \in F$$ (It is immediate with our defintion of the internal multiplication of [F]). 
*)

Context `{Fr : Ring}.

Lemma subring_criteria_2 : Fprop Eone.
Proof.
    (* TODO ! *)
Admitted.

(**
For subfields, we prove that  $$\forall x \in F, x \neq 0 \Rightarrow x^{-1} \in F$$.
*)

Lemma subfield_criteria_2 : forall (x: ApartZero E), Fprop ([-1] x).
Proof.
    (* TODO ! *)
Admitted.

End second_implication.

End Substructures_criteria.

End Substructures_definition.

(**
** Theorems
*)

Section Substructures_theorems.

Variable E:Set.
Context {Ee : Equiv E} {Eequiv_refl : Reflexive Ee} {Ezero : Zero E} {Eplus : Plus E}
    {Eplus_assoc : Associative Eplus} {Ezero_left : LeftIdentity Eplus Ezero}
    {Ezero_right : RightIdentity Eplus Ezero} {Enegate : Negate E} 
    {Enegate_proper : Proper (respectful Ee Ee) Enegate} {Eg : Group E}
    {Eplus_proper : Proper (Ee ==> Ee ==> Ee) plus}
    {Ezero_right_inverse : RightInverse Eplus Enegate Ezero}
    {Ezero_left_inverse : LeftInverse Eplus Enegate Ezero}.

Let Fprop (x:E) := True.
Lemma Fprop_full : full_sig E Fprop.
Proof.
    repeat red. auto.
Qed.

Let inj := sig_injection E Fprop.
Let F:= sig Fprop.

Instance Fplus_closed : ClosedOp E Fprop plus.
    repeat red. auto.
Defined.

Instance Fzero0 : Zero F.
    refine (exist Fprop Ezero _). unfold Fprop ; auto.
Defined.

Instance Fnegate0 : Negate F.
    unfold Negate ; refine (fun x => exist Fprop ([--] (inj x)) _).
    unfold Fprop ; auto.
Defined.

Theorem group_is_subgroup : Group E -> SubGroup E Fprop.
Proof.
    intros. repeat split ; auto ; (repeat (unfold equiv ; unfold Fe ; auto)) ;
        unfold Fprop ; repeat red ; intros.
    apply Eplus_assoc. apply Eplus_proper ; auto.
    apply Ezero_left. apply Ezero_right.
    apply Enegate_proper ; auto.
    apply Ezero_left_inverse. apply Ezero_right_inverse.
Qed.

End Substructures_theorems.

(**
* Applications
*)

Section Substructures_applications.

Require Export MathClasses.implementations.ZType_integers.
Context {zdistr : RightDistribute mult plus}.
(**
We define $$a \mathbb{Z} = \{ a \cdot k \mid k \in \mathbb{Z} \}$$ (with $$a \in \mathbb{Z}$$), 
and we prove that $$(a \mathbb{Z}, \cdot)$$ is a sub-group of $$(\mathbb{Z}, \cdot)$$. 
*)

Variable a:Z.
Definition z_in_aZ (z:Z) : Prop := exists (k : Z), z [=] k [*] a.
Let aZ := sig z_in_aZ.
Let inj := sig_injection Z z_in_aZ.

(**
The identity of $$(\mathbb{Z}, \cdot)$$ belongs to $$a \mathbb{Z}$$. 
*)
Lemma zero_in_aZ : z_in_aZ [0].
Proof.
    exists 0 ; simpl ; reflexivity.
Qed.
Instance aZ_Zero : Zero aZ := Fzero _ _ zero_in_aZ.

(**
$$a \mathbb{Z}$$ is closed under $$\mathbb{Z}$$ addition :
*)
Instance aZ_add_closed : ClosedOp Z z_in_aZ plus.
Proof.
    destruct x, y ; unfold z_in_aZ in z, z0 ; destruct z, z0 ;  exists (x1 [+] x2) ; simpl. 
    rewrite e, e0. rewrite zdistr. reflexivity.
Qed.

Lemma aZ_negate : forall x : aZ, z_in_aZ ([--] inj x).
Proof.
    intros ; unfold z_in_aZ ; destruct x ; destruct z.
    exists ([--] x0). simpl. rewrite e. unfold mult, negate. 
      unfold stdlib_binary_integers.Z_mult, stdlib_binary_integers.Z_negate. 
      rewrite Z.mul_opp_l ; reflexivity.
Qed.

Instance aZ_neg : Negate aZ := Fnegate _ _ aZ_negate.

Instance aZ_subgroup : SubGroup Z z_in_aZ.
    apply subgroup_criteria_1.
Defined.

End Substructures_applications.
