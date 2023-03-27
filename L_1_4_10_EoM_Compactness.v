Require Import Logic_and_Set_Theory.
Require Import EoM_Zorns_Lemma.
Require Import L_1_4_10_EoM_Intro.
From Coq Require Import Powerset_facts.
From Coq Require Import Finite_sets.
From Coq Require Import Powerset_Classical_facts.
From Coq Require Import Finite_sets_facts.
From Coq Require Import Constructive_sets.




Theorem Compactness : forall (Gamma : Ensemble Formula) (f:Formula),
ND Gamma f -> (exists Gamma' : Ensemble Formula, 
Finite Formula Gamma' /\ ND Gamma' f /\ Inc Gamma' Gamma).
Proof. intros Gamma f H. Admitted.

