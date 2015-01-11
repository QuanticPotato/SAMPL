Require Import CoRN.algebra.CRings.

Require Export SAMPL.lists.
Require Export SAMPL.integers.

(**
* Definitions
*)

Section Polynomials_definitions.

Variable K : CRing.

(**
We define a polynomial [P] as an integers sequence 
$$(c_i)_{i \in \mathbb{N}} \in K^{\mathbb{N}}$$, such as the $$c_i$$ are all zero from a 
certain index. We then note this polynomial : 
$$P = \sum\limits_{i = 0}^{i_o} c_i X^i = \sum\limits_{i \geq 0} c_i X^i$$
*)

Definition polynomial := list K.

(**
We define basic operations on polynomials intuitively :
We pose $$P = \sum\limits_{i \geq 0} c_i X^i$$ and $$Q = \sum\limits_{i \geq 0} d_i X^i$$, 
- The addition is just the sum of the sequences :  $$P + Q = \sum\limits_{i \geq 0} (c_i + d_i) X^i$$
- Multiplication by a constant : $$\lambda P  = \sum\limits_{i \geq 0} \lambda c_i X^i$$
- Product of two polynomials : The sum of the multiplications of [Q] with every coefficient of [P].
It results in : $$PQ = \sum\limits_{i\geq 0}(\sum\limits_{j=0}^i c_j d_{i-j}) X^i$$
*)

Definition plus_poly (p q : polynomial) : polynomial := 
    (list_map2 K csg_op p q [0]).

Definition mult_poly_const (p : polynomial) (lambda : K) : polynomial :=
    (map (fun (x:K) => lambda [*] x) p).

Definition mult_poly (p q : polynomial) : polynomial :=
    (fix loop (p q : polynomial) :=
        match p with
            | nil => nil
            | c::p' => plus_poly (mult_poly_const q c) (([0])::(loop p' q))
        end) p q.

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
        | nil => (n = nat_mInf)
        | c::p' => (c [#] [0]) and (forall (n' : nat), poly_coeff_nth p n' [=] [0])
    end.

End Polynomials_definitions.