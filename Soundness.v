Require Import Logic_and_Set_Theory.
From Coq Require Import Sets.Ensembles.
From Coq Require Import Sets.Powerset_facts.
From Coq Require Import Bool.
From Coq Require Import Constructive_sets.


Lemma Oral: forall (f1 f2 : bool),
(orb f1 f2) = true <-> (f1 = false -> f2 = true) \/ (f2 = false -> f1 = true) \/ ( f1=true /\ f2=true ).
Proof.
Admitted.
Lemma Classic_or : forall (f1 f2: bool),
(orb f1 f2) = true <-> (f1 = true /\ f2 = false) \/ (f2 = true /\ f1 = false) \/ (f1 = true /\ f2 = true).
Proof. split.
-intros H. destruct f1. destruct f2. 
+right. right. split. ++reflexivity. ++reflexivity. 
+left. split. ++reflexivity. ++reflexivity.
+right. left. split. ++apply orb_true_iff in H. destruct H. +++discriminate. +++apply H. ++reflexivity.
-destruct f1. destruct f2.
+intros H. simpl. reflexivity.
+intros H. simpl. reflexivity.
+intros H. destruct H. ++destruct H. discriminate. ++ destruct H. +++destruct H. rewrite -> H.
simpl. reflexivity. +++destruct H. discriminate.
Qed.


Theorem Soundness: forall (Gamma:Ensemble Formula) (f:Formula) , 
ND Gamma f -> sfSf Gamma f.
Proof.
    
    intros Gamma f H.
    unfold sfSf.    
    intros model H1.
    induction H.
    +apply H1. apply H.
    +apply IHND in H1. simpl in H1. apply andb_true_iff in H1. apply H1.
    +apply IHND in H1. simpl in H1. apply andb_true_iff in H1. apply H1.
    +assert (H2: mSsf model C). -apply H1. -apply IHND1 in H1. apply IHND2 in H2.
    simpl. apply andb_true_iff. split. --apply H1. --apply H2.
    +assert (H1':mSsf model C). -apply H1.
    -apply IHND3 in H1. simpl in H1. apply orb_true_iff in H1. destruct H1.
    --apply IHND1. unfold mSsf. intros f0. unfold mSsf in IHND1. unfold mSsf in H1'.
    intros H3. apply Union_inv in H3. destruct H3. ---apply H1'. apply H3.
    ---apply Singleton_inv in H3. rewrite <- H3. apply H1.
    --apply IHND2. unfold mSsf. intros f0. unfold mSsf in IHND1. unfold mSsf in H1'.
    intros H3. apply Union_inv in H3. destruct H3. ---apply H1'. apply H3.
    ---apply Singleton_inv in H3. rewrite <- H3. apply H1.
    +simpl. apply orb_true_iff. left. apply IHND. apply H1.
    +simpl. apply orb_true_iff. right. apply IHND. apply H1.
    +assert (H2:mSsf model C). -apply H1. -apply IHND1 in H1. apply IHND2 in H2.
    simpl in H1.  apply orb_true_iff in H1. destruct H1. apply negb_true_iff in H1.
    --rewrite -> H1 in H2. discriminate. --apply H1.
    +assert (forall b : bool, b=true \/ b=false).
    -intros b. destruct b. --left. reflexivity. --right. reflexivity.
    -assert (val model f1 = true \/ val model f1 = false).
    --apply H0. --destruct H2.
    ---simpl. apply orb_true_iff. right. apply IHND. 
    unfold mSsf. intros f H3. apply Union_inv in H3.
    destruct H3. ----apply H1. apply H3.
    ----apply Singleton_inv in H3. rewrite <- H3. apply H2.
    ---simpl. apply orb_true_iff. left. apply negb_true_iff. apply H2. 
    +simpl. assert (H2:mSsf model C). ++apply H1. ++apply IHND1 in H1. apply IHND2 in H2.
    simpl in H2. rewrite -> H1 in H2. simpl in H2. apply H2.
    +assert (mSsf model
    (Union Formula C (Singleton Formula f)) -> False).
    -intros H2. apply IHND in H2. simpl in H2. discriminate.
    -assert (val model f = true -> False).
    --intros H3. apply H0. unfold mSsf. intros f0 H4.
    apply Union_inv in H4. destruct H4.
    ---apply H1 in H2. apply H2.
    ---apply Singleton_inv in H2. rewrite <- H2. apply H3.
    --simpl. apply negb_true_iff. assert (forall b:bool, b=true \/ b=false).
    ---intros b. destruct b. ----left. reflexivity. ----right. reflexivity.
    ---assert (HL:val model f = true \/ val model f = false).
    ----apply H3. ----destruct HL.
    -----apply H2 in H4. exfalso. apply H4.
    -----apply H4.  
    +apply IHND in H1. simpl in H1. discriminate.
    +assert (mSsf model
    (Union Formula C (Singleton Formula (neg f))) -> False).
    -intros H2. apply IHND in H2. simpl in H2. discriminate.
    -assert (val model (neg f) = true -> False).
    --intros H2. apply H0. unfold mSsf. intros f0 H3.
    apply Union_inv in H3. destruct H3.
    ---apply H1. apply H3. ---apply Singleton_inv in H3. rewrite -> H3 in H2. apply H2.
    --assert (forall b:bool, b=true \/ b=false).
    ---intros b. destruct b. ----left. reflexivity. ----right. reflexivity.
    ---assert (HL:val model (neg f) = true \/ val model (neg f) = false).
    ----apply H3. ----destruct HL.
    -----apply H2 in H4. exfalso. apply H4. -----simpl in H4.
    apply negb_false_iff in H4. apply H4.

