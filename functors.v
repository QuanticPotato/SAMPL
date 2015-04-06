(***********************************************************************
*  ____   __   _  _  ____  __    *     Still Another Math library !    *
* / ___) / _\ ( \/ )(  _ \(  )   *-------------------------------------*
* \___ \/    \/ \/ \ ) __// (_/\ *        (c) Chauvin Barnabé          *
* (____/\_/\_/\_)(_/(__)  \____/ *  This file is distributed under the *
*                                *  terms of the GPL License Version 2 *
***********************************************************************)

Require Export SAMPL.structures.

Open Scope nat.

Global Generalizable All Variables.

(**
* Sums
In this section, we define the operator $$\sum$$.
*)

Section sums.

Context E {Ee : Equiv E} {Ezero : Zero E} {Eplus : Plus E} {Eopp : Negate E} {Eg : AbGroup E}.

(** 
$$\sum\limits_{0<i<=k} \lambda_i$$.
*)
Fixpoint sum (k : nat) (lambda : nat -> E) : E :=
    match k with
        | 0 => [0]
        | S p => (lambda p) [+] (sum p lambda)
    end.

(**
$$\sum\limits_{p<i<=q} \lambda_i$$.
*)
Definition sum' (p q : nat) (lambda : nat -> E) : E :=
    sum (q - p) (fun n => lambda (n + p)).

End sums.

(**
* Products
In this section, we define the operator $$\prod$$.
*)

Section products.

(*(** 
$$\prod\limits_{0<i<=k} \lambda_i$$.
*)
Fixpoint prod (k : nat) (lambda : nat -> R) : R :=
    match k with
        | 0 => 1%R
        | S p => ((lambda p) * (prod p lambda))%R
    end.

(**
$$\prod\limits_{p<i<=q} \lambda_i$$.
*)
Definition prod' (p q : nat) (lambda : nat -> R) : R :=
    prod (q - p) (fun n => lambda (n + p)%nat).

(**
$$\prod\limits_{0<=i<=j<=n} \lambda_{i, j}$$.
*)
Fixpoint prod2 (n:nat) (lambda : nat -> nat -> R) : R := 
    let aux := fix aux(n:nat) (k:nat) (lambda:nat->nat->R) :=
        match k with
            | 0 => 1%R
            | S p => ((prod' p n (fun j => lambda p j)) * (aux n p lambda))%R
        end in
        aux n n lambda.

(**
$$\prod\limits_{p<=i<=j<=q} \lambda_{i, j}
*)
Definition prod2' (p q : nat) (lambda : nat -> nat -> R) : R :=
    prod2 (q - p) (fun i j => lambda (i + p)%nat j).

Variable n:nat.

Lemma minus_0 : forall (n:nat), (n-0) = n.
Proof. 
    intros. case n0 ; auto.
    (* TODO *)
Admitted.

Lemma plus_0 : forall n:nat, (n+0) = n.
Proof. 
    (* TODO *)
Admitted.

Lemma prod'_mult : forall (l:nat->R)(p:nat), prod' p n l = ((l p) * (prod' (p+1) n l))%R.
Proof.
    intros. unfold prod'. unfold prod at 1.
Check nat_ind.
elim (n-p). admit.


Lemma prod'_prod : forall (l : nat -> R), prod' 0 n l = prod' (0 + 1) n l.
Proof.
    intros. unfold 

Lemma lambda_eq : forall (l:nat->R)(n1 n2: nat -> nat), 
    n1 = n2 -> (fun n => l (n1 n)) = (fun n => l (n2 n)).
Proof.
    intros. 
    (* On raisonne d'abord sur les elements *)
        assert (forall n:nat, ((fun n0 : nat => l (n1 n0)) n) = ((fun n0 : nat => l (n2 n0)) n)).
        intros. assert (n1 n0 = n2 n0) by (now apply equal_f). now rewrite H0.
    (* Puis, comme on admet l'extensionalité fonctionnelle *)
        apply functional_extensionality. assumption.
Qed.

Lemma lambda_eq_0 : forall (l:nat->R), l = (fun n => l (n + 0)).
Proof.
    intros. apply (lambda_eq l (fun n => n) (fun n => n + 0)).
    apply functional_extensionality. auto.
Qed.

Lemma prod_equiv : forall l : (nat -> R), prod n l = prod' 0 n l.
Proof.
    intros. unfold prod'. rewrite minus_0. rewrite <- lambda_eq_0.
    reflexivity.
Qed.

(** 
$$ \prod\limits_{k = 0}^0 \lambda_k = 0$$
*)
Lemma prod_0 : forall (lambda : nat->R), prod 0 lambda = 1%R.
Proof.
    intros ; unfold prod ; reflexivity.
Qed.

(**
$$ \prod\limits_{k=p}^{n} \lambda_k = \prod\limits_{k = 0}^{n - p} \lambda_{k+p}$$
*)
Lemma prod_decalage : forall (p:nat),  (forall l : (nat -> R),
    (prod' p n l) = (prod' 0 (n - p) (fun n => l (n+p)))).
Proof.
    intros. 
    assert ((fun n0 : nat => l (n0 + 0 + p)) = ((fun n0 : nat => l (n0 + p)))).
        apply (lambda_eq l (fun n => n + 0 + p) (fun n => n + p)).
        apply functional_extensionality. auto.
    unfold prod'. rewrite minus_0. pattern (fun n0 : nat => l (n0 + 0 + p)).
    rewrite H. reflexivity.
Qed.

(** Relation de chasle **)
*)

End products.
