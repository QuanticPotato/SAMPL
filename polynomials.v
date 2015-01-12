Require Import CoRN.algebra.CRings.

Require Export SAMPL.lists.
Require Export SAMPL.integers.

(**
* Definitions
*)

Section Polynomials_definitions.

Variable K : CRing.

(**
** Definition of a polynomial and its operations
*)

(**
We define a polynomial [P] as an integers sequence 
$$(c_i)_{i \in \mathbb{N}} \in K^{\mathbb{N}}$$, such as the $$c_i$$ are all zero from a 
certain index. We then note this polynomial : 
$$P = \sum\limits_{i = 0}^{i_o} c_i X^i = \sum\limits_{i \geq 0} c_i X^i$$
*)

Definition polynomial := list K.
Definition zero_polynomial := nil (A:=K).
Definition one_polynomial := ([1])::(nil (A:=K)).

(** 
In the following, we pose $$P = \sum\limits_{i \geq 0} c_i X^i$$ and $$Q = \sum\limits_{i \geq 0} d_i X^i$$.
*)

(**
Equality over polynomials with our definition is quite simple : 
- [P] is 0 iff $$\forall i \geq, c_i = 0$$
- [P] equals [Q] iff $$\forall i \geq 0, c_i = d_i$$
- [P] is apart [Q] iff $$\exists i \geq 0, c_i \neq d_i$$
*)

Definition poly_is_zero (p : polynomial) : Prop := list_all_predicate K (fun x => x [=] [0]) p.

Definition poly_eq (p q : polynomial) : Prop := 
    (fix loop (p q : polynomial) :=
        match p, q with
            | nil, _ => poly_is_zero q
            | _, nil => poly_is_zero p
            | a::t, a'::t' => (a [=] a') /\ (loop t t')
        end) p q.

Definition poly_apart (p q : polynomial) : Prop := ~ (poly_eq p q).

(**
We define basic operations on polynomials intuitively :
We pose $$P = \sum\limits_{i \geq 0} c_i X^i$$ and $$Q = \sum\limits_{i \geq 0} d_i X^i$$, 
- The addition is just the sum of the sequences :  $$P + Q = \sum\limits_{i \geq 0} (c_i + d_i) X^i$$
- The opposite : $$-P = \sum\limits_{i \geq 0} - c_i X^i$$
- Multiplication by a constant : $$\lambda P  = \sum\limits_{i \geq 0} \lambda c_i X^i$$
- Product of two polynomials : The sum of the multiplications of [Q] with every coefficient of [P].
It results in : $$PQ = \sum\limits_{i\geq 0}(\sum\limits_{j=0}^i c_j d_{i-j}) X^i$$
*)

Definition poly_plus (p q : polynomial) : polynomial := 
    (list_map2 K csg_op p q [0]).

Definition poly_opp (p : polynomial) : polynomial :=
    (list_map K cg_inv p).

Definition poly_mult_const (p : polynomial) (lambda : K) : polynomial :=
    (map (fun (x:K) => lambda [*] x) p).

Definition poly_mult (p q : polynomial) : polynomial :=
    (fix loop (p q : polynomial) :=
        match p with
            | nil => nil
            | c::p' => poly_plus (poly_mult_const q c) (([0])::(loop p' q))
        end) p q.

(**
** ([polynomial K], [plus_poly], [mult_poly]) is a ring
In this section, we prove that polynomials form a constructive ring, with the polynomial addition and 
the polynomial multiplication. This include proving they form a Setoid, a SemiGroup, a Monoid, a Group
and finally a ring.
*)

Section polynomial_ring.

(**
The polynomials form a constructive setoid, with [poly_eq] as equality relation :
*)

Lemma ap_poly_irreflexive : irreflexive poly_apart.
Admitted.
Lemma ap_poly_symmetric : Csymmetric poly_apart.
Admitted.
Lemma ap_poly_cotransitive : cotransitive poly_apart.
Admitted.
Lemma ap_poly_tight : tight_apart poly_eq poly_apart.
Admitted.
Definition ap_poly_is_apartness := Build_is_CSetoid polynomial poly_eq poly_apart
    ap_poly_irreflexive ap_poly_symmetric ap_poly_cotransitive ap_poly_tight.

Definition poly_as_CSetoid := Build_CSetoid _ _ _ ap_poly_is_apartness.

(**
The polynomials form a constructive semi-group, with [poly_plus] as addition.
They also form a constructive semi-group, with [poly_mult] as addition :
*)

Lemma poly_plus_well_defined : bin_fun_wd poly_as_CSetoid poly_as_CSetoid poly_as_CSetoid poly_plus.
Admitted.
Lemma poly_plus_strong_ext : bin_fun_strext poly_as_CSetoid poly_as_CSetoid poly_as_CSetoid poly_plus.
Admitted.
Definition poly_plus_is_bin_fun := Build_CSetoid_bin_fun poly_as_CSetoid poly_as_CSetoid poly_as_CSetoid
    poly_plus poly_plus_strong_ext.
Lemma poly_plus_is_CSemiGroup : is_CSemiGroup poly_as_CSetoid poly_plus_is_bin_fun.
Admitted.
Lemma poly_plus_is_assoc : associative poly_plus_is_bin_fun.
Admitted.

Lemma poly_mult_well_defined : bin_fun_wd poly_as_CSetoid poly_as_CSetoid poly_as_CSetoid poly_mult.
Admitted.
Lemma poly_mult_strong_ext : bin_fun_strext poly_as_CSetoid poly_as_CSetoid poly_as_CSetoid poly_mult.
Admitted.
Definition poly_mult_is_bin_fun := Build_CSetoid_bin_fun poly_as_CSetoid poly_as_CSetoid poly_as_CSetoid 
   poly_mult poly_mult_strong_ext.
Lemma poly_mult_is_CSemiGroup : (is_CSemiGroup poly_as_CSetoid poly_mult_is_bin_fun).
Admitted.
Lemma poly_mult_is_assoc : associative poly_mult_is_bin_fun.
Admitted.

Definition poly_as_CSemiGroup := Build_CSemiGroup _ poly_plus_is_bin_fun poly_plus_is_assoc.
Definition poly_mult_as_CSemiGroup := Build_CSemiGroup _  poly_mult_is_bin_fun poly_mult_is_assoc.

(**
The polynomials form a constructive monoid, with [zero_polynomial] as neutral element.
They also form a constructive monoid for the [poly_mult], with [one_polynomial] as neutral element.
*)

Lemma poly_zero_right_neutral : is_rht_unit poly_plus_is_bin_fun zero_polynomial.
Admitted.
Lemma poly_zero_left_neutral : is_lft_unit poly_plus_is_bin_fun zero_polynomial.
Admitted.
Definition poly_is_CMonoid := Build_is_CMonoid poly_as_CSemiGroup _ poly_zero_right_neutral poly_zero_left_neutral.

Lemma poly_one_right_mult_neutral : is_rht_unit poly_mult_is_bin_fun one_polynomial.
Admitted.
Lemma poly_one_left_mult_neutral : is_lft_unit poly_mult_is_bin_fun one_polynomial.
Admitted.
Definition poly_mult_is_CMonoid := Build_is_CMonoid poly_mult_as_CSemiGroup _ poly_one_right_mult_neutral poly_one_left_mult_neutral.

Definition poly_as_CMonoid := Build_CMonoid poly_as_CSemiGroup _ poly_is_CMonoid.
Definition poly_mult_asCMonoid := Build_CMonoid poly_mult_as_CSemiGroup _ poly_mult_is_CMonoid.

(**
The polynomials form a constructive group, with [poly_opp] as opposite of the addition :
*)

Lemma poly_opp_well_defined : fun_wd (S1:=poly_as_CSetoid) (S2:=poly_as_CSetoid) poly_opp.
Admitted.
Lemma poly_opp_strong_ext : fun_strext (S1:=poly_as_CSetoid) (S2:=poly_as_CSetoid) poly_opp.
Admitted.
Definition poly_opp_is_fun := Build_CSetoid_fun poly_as_CSetoid poly_as_CSetoid poly_opp poly_opp_strong_ext.
Lemma poly_is_CGroup : is_CGroup poly_as_CMonoid poly_opp_is_fun.
Admitted.

Definition poly_as_CGroup := Build_CGroup  poly_as_CMonoid poly_opp_is_fun poly_is_CGroup.

(** 
The polynomials form a constructive abelian group :
*)

Lemma poly_is_CAbGroup : is_CAbGroup poly_as_CGroup.
Admitted.

Definition poly_as_CAbGroup := Build_CAbGroup poly_as_CGroup poly_is_CAbGroup.

(**
The polynomials form a constructive ring, with [poly_mult] as multiplication :
*)

Lemma poly_mult_is_commut : commutes poly_mult_is_bin_fun.
Admitted.
Lemma poly_mult_plus_is_distr : distributive poly_mult_is_bin_fun poly_plus_is_bin_fun.
Admitted.
Lemma poly_one_neq_zero : poly_apart zero_polynomial one_polynomial.
Admitted.
Definition poly_is_CRing := Build_is_CRing poly_as_CAbGroup _ _ poly_mult_is_assoc 
    poly_mult_is_CMonoid poly_mult_is_commut poly_mult_plus_is_distr poly_one_neq_zero.

Definition poly_as_CRing := Build_CRing _ _ _ poly_is_CRing.

End polynomial_ring.

(**
** Properties of polynomials
*)

(**
We define the coefficient of the [n]th degree :
(It's just the value at index [n] in the sequence)
If the [n] bigger than the polynomial degree, then the [n]th coefficient is the [K]'s neutral element.
*)

Definition poly_coeff_nth (p : polynomial) (n : nat) : K :=
    nth n p [0].

(**
We define the degree of a polynomial :
$$\mathrm{deg}(P) =  = \left\{\begin{tabular}{l} $P=0$ : $max(\{i \in \mathbb{N}, c_i \neq 0\}$)
\\ $P=0$ : $-\infty$ \end{tabular}\right.$$
*)

Definition poly_degree (p : polynomial) (n : nat_inf) : CProp :=
    match p with
        | nil => False
        | c::p' => (c [#] [0]) and (forall (n' : nat), poly_coeff_nth p n' [=] [0])
    end.

End Polynomials_definitions.

(**
* Theorems
*)

Section Polynomials_theorems.

(**
In the following section, we assume the polynomials are non-zero (Unless otherwise stated).
The polynomial degrees are then finite. (The zero cases are trivial to prove)
*)

Variable K : CRing.
Variables P Q : polynomial K.

Variables nP nQ : nat.
Hypothesis Pdegree : forall (n : nat_inf), poly_degree K P n -> nat_is_finite n nP.
Hypothesis Qdegree : forall (n : nat_inf), poly_degree K Q n -> nat_is_finite n nQ.

Theorem poly_deg_sum : forall (n : nat_inf), poly_degree K (plus_poly P Q) n 
    -> forall (n' : nat), nat_is_finite n n' -> 