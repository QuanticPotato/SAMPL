(***********************************************************************
*  ____   __   _  _  ____  __    *     Still Another Math library !    *
* / ___) / _\ ( \/ )(  _ \(  )   *-------------------------------------*
* \___ \/    \/ \/ \ ) __// (_/\ *        (c) Chauvin Barnabé          *
* (____/\_/\_/\_)(_/(__)  \____/ *  This file is distributed under the *
*                                *  terms of the GPL License Version 2 *
***********************************************************************)

Require Export ZArith.

Require Export SAMPL.sets.

(**
* Definitions
*)

(**
Sometime, it is usefull to manipulate $$\infty$$ (For $$\mathbb{N}$$, this is the upper bound : $$+\infty$$ for example).
We then define the [*_pInf] and [*_mInf] predicate that indicates whether [n] is infinity or not. (The tricky point is that 
we cannot define an extra symbol, because we want to keep the integer ([nat] or [Z] type) :
- [x] is $$+\infty$$ if $$\forall y \in \mathbb{Z}, x > y$$
- [x] is $$-\infty$$ if $$\forall y \in \mathbb{Z}, x < y$$
(We also define these definition for $$\mathbb{N}$$). 

One must be aware that these predicates only give an equivalent of the
math symbol $$-\infty$$ and $$+\infty$$. They should only be used for conventions (Otherwise it is totally incoherent).
*)

Definition nat_pInf (n : nat) : Prop := forall (n' : nat), n > n'.

Definition nat_mInf (n : nat) : Prop := forall (n' : nat), n < n'.

Definition Z_pInf (x : Z) : Prop := forall (y : Z), (x > y)%Z.

Definition Z_mInf (x : Z) : Prop := forall (y : Z), (x < y)%Z.
