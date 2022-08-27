Require Import Logic_and_Set_Theory.
Require Import EoM_Zorns_Lemma.
Require Import L_1_4_10_EoM_Intro.
From Coq Require Import Powerset_facts.
From Coq Require Import Finite_sets.
From Coq Require Import Powerset_Classical_facts.
From Coq Require Import Finite_sets_facts.
From Coq Require Import Constructive_sets.


Lemma Ex_of_Max1:forall (Gamma : Ensemble Formula),
Cons Gamma -> (exists (Gammap : Ensemble Formula), maximal (Ensemble Formula) (TheS Gamma) Gammap Inc).
Proof. intros Gamma H. case Zorn's_Lemma with (U:=Ensemble Formula) (S:=TheSet Gamma) (R:=Inc).
+unfold pao. split.
-unfold reflexive. intros x. unfold Inc. unfold Included. intros x0 H1. apply H1.
-split. 
--unfold transitive. intros x y z H1 H2.  unfold Inc in H1. unfold Inc in H2. unfold Inc.
unfold Included in H1. unfold Included in H2. unfold Included.
intros x0 H3. apply H1 in H3. apply H2 in H3. apply H3.
--unfold antisymmetric. intros x y H1 H2. apply Extensionality_Ensembles.
unfold Same_set. unfold Inc in H1. unfold Inc in H2. split. ---apply H1. --- apply H2.
+intros T H1. exists (PropUoCE2 T) . unfold upper_bound. split.
-intros X H2. unfold Inc. unfold Included. intros f.
    intros H3. apply About_PropUoCEr. unfold PropUoCE2.
    exists X. split. --apply H2. --apply H3.
-apply About_TheSet. split.
--apply PropUoCE_Inclusion. ++ apply H1. 
++intros f H2. unfold PropUoCE2.  
unfold PropUoCE2. case Chains_Are_Nonempty with (T:=T) (Gamma:=Gamma).
---apply H1. --- intros Gamma' H3. exists Gamma'. split.
+++ apply H3. 
+++assert (H4:Inc Gamma Gamma').
----apply H1. apply H3. ----apply H4. apply H2.


--unfold Cons. apply pbc. intros H0. apply dnegE in H0.
apply Compactness in H0. destruct H0. rename x into Gamma'.
destruct H0. destruct H2. 
assert (H4: chain (Ensemble Formula) Inc (TheSet Gamma) T /\ Inc Gamma' (PropUoCE2 T) /\ Finite Formula Gamma'  ).
*split. apply H1. split. apply H3. apply H0.
*apply UoCE1_has_subset in H4. destruct H4. rename x into Gamma''.
destruct H4. assert (H6:Cons Gamma'').
**apply About_chain_in_TheSet with (T:=T) (Gamma := Gamma). split.
*** apply H1. ***apply H4.
**assert (H7: ND Gamma'' bot). 
***apply Strong_Weakening with (Pi:=Gamma').  
****apply H2. ****apply H5.
***contradiction.

+intros x H1. exists x. apply H1.
Qed.


