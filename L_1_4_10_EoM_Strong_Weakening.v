Require Import Logic_and_Set_Theory.
Require Import EoM_Zorns_Lemma.
Require Import L_1_4_10_EoM_Intro.
From Coq Require Import Powerset_facts.
From Coq Require Import Finite_sets.
From Coq Require Import Powerset_Classical_facts.
From Coq Require Import Finite_sets_facts.
From Coq Require Import Constructive_sets.



Lemma Strong_Weakening: forall (Pi : Ensemble Formula) (f : Formula), ND Pi f -> forall (Gamma : Ensemble Formula), Inc Pi Gamma -> ND Gamma f.
Proof.
    intros Pi f H. induction H; intros.
    -apply ax. apply H0. apply H.
    -apply conjE1 with (f2:=f2). apply IHND. apply H0.
    -apply conjE2 with (f1:=f1). apply IHND. apply H0.
    -apply conjI.
        +apply IHND1. apply H1.
        +apply IHND2. apply H1. 
    -apply disjE with (f1:=f1) (f2:=f2).
        +apply IHND1. apply incl_add. apply H2.
        +apply IHND2. apply incl_add. apply H2.
        +apply IHND3. apply H2.
    -apply disjI1. apply IHND. apply H0.
    -apply disjI2. apply IHND. apply H0.
    -apply impE with (f1:=f1).
        +apply IHND1. apply H1.
        +apply IHND2. apply H1.
    -apply impI. apply IHND. apply incl_add. apply H0.
    -apply negE with (f:=f). 
        +apply IHND1. apply H1.
        +apply IHND2. apply H1.
    -apply negI. apply IHND. apply incl_add. apply H0.
    -apply botE. apply IHND. apply H0.
    -apply RAA. apply IHND. apply incl_add. apply H0.
    Qed.

