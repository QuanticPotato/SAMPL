Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.canonical_names.

Global Generalizable All Variables.

(**
* Defnitions
*)

(**
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

(**
We first define the scalar multiplication. 
The addition is already defined : we use [Plus] of a semiring.
*)

Class ScalarMult K E := scalar_mult : K -> E -> E.


Section vector_space_def.

Context K {Ke : Equiv K} {Kplus : Plus K} {Kmult : Mult K} {Kzero : Zero K} {Kone : One K}
    {Knegate : Negate K} {Kap : Apart K} {Krecip : Recip K} {Kf : Field K}.

Context E {Ee : Equiv E} {Eop : SgOp E} {Eunit : MonUnit E} {Eneg : Negate E} {Eg : AbGroup E}.

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
    vs_add_ass : Associative (&) ;
    vs_add_comm : Commutative (&) ;
    vs_add_id : LeftIdentity (&) mon_unit ;
    vs_add_inv : Negate E ;
    vs_scalar_mult_comp : ScalarMultCompatibility ;
    vs_scalar_mult_id : LeftIdentity scalar_mult one ;
    vs_scalar_mult_distr_vector : ScalarMultDistr_Vector ;
    vs_scalar_mult_distr_field : ScalarMultDistr_Field
}.

End vector_space_def.
