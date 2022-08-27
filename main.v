Require Import Logic_and_Set_Theory.
Require Import EoM_Zorns_Lemma.
Require Import L_1_4_11_EoM_Existence_of_Model.
Require Import L_1_4_10_EoM_Intro.
Require Import L_1_4_10_EoM_Strong_Weakening.
Require Import L_1_4_10_EoM_Second_Lemma.
Require Import L_1_4_10_EoM_main.
Require Import L_1_4_10_EoM_Compactness.
From Coq Require Import Powerset_facts.
From Coq Require Import Finite_sets.
From Coq Require Import Powerset_Classical_facts.
From Coq Require Import Finite_sets_facts.
From Coq Require Import Constructive_sets.



Lemma UnionR : forall (Gamma:Ensemble Formula) (f:Formula) (model: nat -> bool),
mSsf model (Union Formula Gamma (Singleton Formula(neg f))) ->(mSsf model Gamma  /\ val model f = false).
Proof.
    intros Gamma f model H.
    split.
    +unfold mSsf. unfold mSsf in H.
        intros f0 H1. apply H. apply Union_introl.  
        apply H1.
    +unfold mSsf in H. 
        assert (H1: val model (neg f) = true -> val model f = false).
        {intros H2. simpl in H2. assert (H3:forall (b:bool), negb b=true -> b= false).
        {intros b. intros H4. induction b. +simpl in H4. rewrite -> H4. reflexivity.
        +reflexivity.  }
        apply H3 in H2.
        apply H2. }
        apply H1. apply H. apply Union_intror. apply In_singleton. 
        
Qed.




(*The Theorem!!!*)
Theorem Completeness: forall (Gamma:Ensemble Formula) (f:Formula) , 
sfSf Gamma f -> ND Gamma f.
Proof.
intros Gamma f. intros H.
apply pbc. intros H1. apply ConsSyns in H1. 
apply Existence_of_Model in H1.
inversion H1.
apply UnionR in H0. 
unfold sfSf in H. destruct H0. apply H in H0.
rewrite -> H2 in H0. discriminate.
Qed.


    



