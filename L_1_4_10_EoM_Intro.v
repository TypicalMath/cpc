Require Import Logic_and_Set_Theory.
Require Import EoM_Zorns_Lemma.
From Coq Require Import Ensembles.

Definition Inc : relation (Ensemble Formula) := Included Formula.

Lemma Inc_is_pao : pao (Ensemble Formula) Inc.
unfold pao. split.
+unfold Inc. unfold reflexive. intros Gamma. unfold Included.
intros f H. apply H.
+split.
++unfold transitive. intros x y z H1 H2. unfold Inc. unfold Included.
intros f H3. unfold Inc in H1. unfold Inc in H2. unfold Included in H1.
unfold Included in H2. apply H1 in H3. apply H2 in H3. apply H3.
++unfold antisymmetric. intros x y H H1.
unfold Inc in H. unfold Inc in H1.
apply Extensionality_Ensembles. unfold Same_set. unfold Inc in H1. split. ---apply H. --- apply H1.
Qed.


(*Union of a Chain's Elements:*)
Definition TheSet(Gamma:Ensemble Formula) (Gammap:Ensemble Formula): Prop:=
    Inc Gamma Gammap /\ Cons Gammap.

Definition TheS (Gamma : Ensemble Formula) : Ensemble (Ensemble Formula):= 
    TheSet Gamma.

Definition PropUoCE (T: Ensemble (Ensemble Formula) ) (Gammap : Ensemble Formula) : Prop :=
forall (Gamma:Ensemble Formula),( In (Ensemble Formula) T Gamma ->
forall (f : Formula), (In Formula Gamma f-> In Formula Gammap f )).

Definition PropUoCE2 (T: Ensemble (Ensemble Formula) ) (f : Formula) : Prop :=
exists (Gamma:Ensemble Formula), (In (Ensemble Formula) T Gamma /\
In Formula Gamma f).

Definition UoCE1 (T: Ensemble (Ensemble Formula)) : Ensemble Formula :=
    PropUoCE2 T.  

Lemma About_PropUoCEr : forall (f:Formula) (T:Ensemble (Ensemble Formula)), 
PropUoCE2 T f -> In Formula (PropUoCE2 T) f.
Proof. intros f T H. apply H. 
Qed.

Lemma About_PropUoCEl : forall (f:Formula) (T:Ensemble (Ensemble Formula)), 
In Formula (PropUoCE2 T) f -> PropUoCE2 T f.
Proof. intros f T H. apply H.
Qed.

Lemma About_TheSet0 : forall (Gamma Gammap: (Ensemble Formula)),
TheSet Gamma Gammap->In (Ensemble Formula) (TheSet Gamma) Gammap.
Proof. intros Gamma Gammap H. apply H.
Qed.

Lemma About_TheSet : forall (Gamma Gammap: (Ensemble Formula)),
Inc Gamma Gammap /\ Cons Gammap->In (Ensemble Formula) (TheSet Gamma) Gammap.
Proof. intros Gamma Gammap H. apply About_TheSet0. unfold TheSet. apply H.
Qed. 

Lemma PropUoCE_Inclusion : forall (T : Ensemble (Ensemble Formula)) (Gamma : Ensemble Formula),
(forall f:Formula, In Formula Gamma f -> PropUoCE2 T f) -> Inc Gamma (PropUoCE2 T).
Proof.
    intros T Gamma H. unfold Inc. unfold Included. intros f H1. 
    assert (H2:PropUoCE2 T f -> In Formula (PropUoCE2 T) f).
    +apply About_PropUoCEl.
    +apply H2. apply H. apply H1.
    Qed.

Lemma About_chain_in_TheSet : forall (T: Ensemble ( Ensemble Formula )) (Gamma Gamma': Ensemble Formula),
chain (Ensemble Formula) Inc (TheSet Gamma) T /\ In (Ensemble Formula) T Gamma' 
-> Cons Gamma'.
Proof. intros T Gamma Gamma' H. apply H. apply H.
Qed.

Axiom Chains_Are_Nonempty : forall (T: Ensemble (Ensemble Formula)) (Gamma:Ensemble Formula),
chain (Ensemble Formula) Inc (TheSet Gamma) T ->
exists Gamma':Ensemble Formula, In (Ensemble Formula) T Gamma'.

Lemma iConsEx : forall  (Gamma : Ensemble Formula),
iCons (Gamma) -> exists f:Formula,
ND Gamma f /\ ND Gamma (neg f).
Proof.
    intros Gamma H. unfold iCons in H. exists bot. split.
    +apply H. +apply negI. apply Weakening. apply H.
    Qed.
