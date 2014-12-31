Require Import ZArith.
Open Scope Z_scope.
Require Import CRings.

(* 1) Algebraic structures
   -----------------------  *)

(* For every algebraic structures, we are using the CoRN definitions. 
   We try to give some basic example on how to use them. (i.e. prove
   than such a set and such a binary operation is a group for example *)

(*   Semi-Group :   CSemiGroup   (in CSemiGroups.v)
     Monoid :       CMonoid      (in CMonoids.v)
     Group :        CGroup       (in CGroups.v)
     Ring :         CRing        (in CRings.v)  *)

(* To build any of these structures, we first have to build their "parent" ones. 
   Then, we simply make a definition [Definition <id> := Build_<struct> <args>].
    - <id> is usually of the form [<set>_as_<struct], like for example Z_as_CRing.
    - <struct> is one of the structures quoted above.
    - <args> are the "parent structure" (i.e. in the hierarchical order) proofs, 
      and the current structure proof. For example if we try to build a CGroup, we 
      must give a proof (i.e. a Definition like the previous one) that assert that 
      it is a CMonoid, and prove the CGroup properties.
   Finaly, the Definition has the type of Build_<struct>, which is <struct>. 
   (This is actually the classical way to build a Record) *)
   

(* First example : Prove that (Z, +, x) is a ring 
   The proofs are already available in CoRN.model, but we'll redo them 
   as example (It is easier to read this file than look for the proofs 
   in the CoRN documentation). *)

(* First of all, prove that (Z, =, \neq) is a constructive Setoid. This is not 
   interesting mathematicaly, so we'll use the CoRN definition [Z_as_CSetoid],
   available in CoRN.model.setoids.Zsetoid *)

(* Then, we prove (Z, +) is a Semi-Group. This include :
     - Proving +*)


(* 2) Sub-structures
   -----------------   *)

Require Import Zgroup.

(* The CoRN library also provide the definitions of the sub-structure (e.g. a
   sub-group, a sub-ring ...). Here are the definitions :
    Sub-Semi-Group :   Build_SubCSemiGroup   (in CSemiGroups.v)
    Sub-Monoid :       Build_SubCMonoid      (in CMonoids.v)
    Sub-Group :        Build_SubCGroup       (in CGroups.v)
    Sub-Ring :         Build_SubCRing        (in CRings.v)  *)

(* To prove a set is a sub-<structure>, we have to provide three things :
     - The structure (For example a Group, if we want to build a Sub-Group
     - A predicate that assert which elements belongs to the new set
     - The proofs that this new set satisfy the sub-<structure> properties
       (e.g., if it is a Sub-Group, proving that the neutral element belong
       to the new set, prove the bin-operation is well defined over the new
       set, and finaly prove that every elements of the new set are symmetrizable *)

(* First example : Prove that (aZ, +) (with a:Z) are a sub-groups of (Z, +) *)

Variable a:Z.
Definition z_in_aZ (z:Z_as_CGroup) : CProp := exists (k : Z), z = k*a.

(* Neutral of (Z,+) belongs to aZ (It's 0) *)
Lemma zero_in_aZ : z_in_aZ [0].
    unfold z_in_aZ ; exists 0 ; simpl ; reflexivity.
Qed.

(* Addition is well defined (i.e. internal) in aZ *)
Lemma plus_aZ : bin_op_pres_pred Z_as_CGroup z_in_aZ Zplus_is_bin_fun.
    unfold bin_op_pres_pred ; unfold z_in_aZ ; intros ; destruct H ; destruct H0. 
    exists (x1 + x0) ; simpl ; rewrite H ; rewrite H0 ; ring.
Qed.

(* Every elements of aZ is symmetrizable with the addition *)
Lemma inv_aZ : un_op_pres_pred Z_as_CGroup z_in_aZ Zopp_is_fun.
    unfold un_op_pres_pred ; unfold z_in_aZ ; intros ; simpl.
    destruct H ; exists (-x0) ; rewrite H ; ring.
Qed.

(* aZ_subgroup_Z has type CGroup *)
Definition aZ_subgroup_Z := Build_SubCGroup Z_as_CGroup z_in_aZ zero_in_aZ plus_aZ inv_aZ.
