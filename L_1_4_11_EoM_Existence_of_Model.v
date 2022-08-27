Require Import Logic_and_Set_Theory.
Require Import EoM_Zorns_Lemma.
Require Import L_1_4_10_EoM_Intro.
From Coq Require Import Powerset_facts.
From Coq Require Import Finite_sets.
From Coq Require Import Powerset_Classical_facts.
From Coq Require Import Finite_sets_facts.
From Coq Require Import Constructive_sets.


(*Function in Lemma 1.4.11:*)

Definition Gamma_Max (Gamma Gammap : Ensemble Formula) : Prop :=
      









(*The Lemma:*)



Lemma Existence_of_Model: forall (Gamma : Ensemble Formula),
~iCons Gamma -> exists (model : nat -> bool), mSsf model Gamma. 
Proof. intros Gamma H. 
