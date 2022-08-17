From Coq Require Import Sets.Ensembles.
From Coq Require Import Powerset_facts.
From Coq Require Import Finite_sets.
(*Formulas: *)

Inductive Formula : Type :=
    | atom : nat -> Formula
    | disj : Formula -> Formula -> Formula
    | conj : Formula -> Formula -> Formula
    | imp : Formula -> Formula -> Formula
    | neg : Formula -> Formula
    | bot : Formula. 

(*Natural Deduction: *)

Inductive ND : Ensemble Formula -> Formula -> Prop :=
    | ax (C:Ensemble Formula) (f: Formula) (H:In Formula C  f) : ND C f
    | conjE1 (C:Ensemble Formula) (f1 f2: Formula) (H:ND C (conj f1 f2)) : ND C f1
    | conjE2 (C:Ensemble Formula) (f1 f2: Formula) (H:ND C (conj f1 f2)) : ND C f2
    | conjI (C:Ensemble Formula) (f1 f2: Formula) (H1:ND C f1) (H2:ND C f2) : ND C (conj f1 f2)
    | disjE (C:Ensemble Formula) (f1 f2 f:Formula) (H1:ND (Union Formula C (Singleton Formula f1)) f) 
        (H2:ND (Union Formula C (Singleton Formula f2)) f) (H3:ND C (disj f1 f2) ): ND C f 
    | disjI1 (C:Ensemble Formula) (f1 f2:Formula) (H:ND C f1):ND C (disj f1 f2)
    | disjI2 (C:Ensemble Formula) (f1 f2:Formula) (H:ND C f2):ND C (disj f1 f2)
    | impE (C:Ensemble Formula) (f1 f2:Formula) (H1:ND C (imp f1 f2)) (H2:ND C (f1)): ND C f2
    | impI (C:Ensemble Formula) (f1 f2:Formula) (H:ND (Union Formula C (Singleton Formula f1)) f2): ND C (imp f1 f2)
    | negE (C:Ensemble Formula) (f :Formula) (H1: ND C f) (H2: ND C (neg f)): ND C bot
    | negI (C:Ensemble Formula) (f :Formula) (H: ND (Union Formula C (Singleton Formula f)) bot ): ND C (neg f) (*Momkene context ghalat bashe!!!*)
    | botE (C:Ensemble Formula) (f:Formula) (H:ND C bot):ND C f
    | RAA (C:Ensemble Formula) (f:Formula) (H:ND (Union Formula C (Singleton Formula (neg f))) bot):ND C f.

(*Hilbert: *)

Inductive Hilb : Ensemble Formula -> Formula -> Prop :=
    | Hax (C:Ensemble Formula) (f: Formula) (H:In Formula C  f) : Hilb C f
    | A1 (C:Ensemble Formula) (f1 f2: Formula)  : Hilb C (imp f1 (imp f2 f1))
    | A2 (C:Ensemble Formula) (f1 f2 f3: Formula)  : Hilb C (imp (imp f1 (imp f2 f3)) (imp (imp f1 f2) (imp f1 f3)))
    | A3 (C:Ensemble Formula) (f1 f2: Formula)  : Hilb C (imp (conj f1 f2) f1)
    | A4 (C:Ensemble Formula) (f1 f2: Formula)  : Hilb C (imp (conj f1 f2) f2)
    | A5 (C:Ensemble Formula) (f1 f2: Formula)  : Hilb C (imp f1 (imp f2 (conj f1 f2)))
    | A6 (C:Ensemble Formula) (f1 f2: Formula)  : Hilb C (imp f1 (disj f1 f2) )
    | A7 (C:Ensemble Formula) (f1 f2: Formula)  : Hilb C (imp f2 (disj f1 f2) )
    | A8 (C:Ensemble Formula) (f1 f2 f3: Formula)  : Hilb C (imp (imp f1 f3) (imp (imp f2 f3) (imp (disj f1 f2) f3)) )
    | A9 (C:Ensemble Formula) (f1: Formula)  : Hilb C (imp bot f1 )
    | A10 (C:Ensemble Formula) (f1: Formula)  : Hilb C (disj f1 (neg f1))
    | MP (C:Ensemble Formula) (f1 f2:Formula) (H1:Hilb C (imp f1 f2)) (H2:Hilb C (f1)): Hilb C f2.

(*Semantics: *)

Fixpoint val  (model : nat -> bool) (f: Formula) : bool:=
    match f with
    | atom n=> model n
    | neg f1 =>  negb(val model f1)
    | disj f1 f2 => orb (val model f1) (val model f2)
    | conj f1 f2 =>andb (val model f1 ) (val model f2)
    | imp f1 f2 => orb(negb(val model f1))  (val model f2)
    | bot => false
    end.

(*a model satisfying a set of formulae*)
(*model|=Gamma*)
Definition mSsf (model : nat -> bool) (Gamma:Ensemble Formula)  : Prop:=
    forall (f:Formula), (In Formula Gamma f -> (val model f = true)).


(*All models satisfying elements of Gamma are satisfying F*)
(*Gamma|=f*)
Definition sfSf (Gamma: Ensemble Formula) (f:Formula) : Prop:=
    forall (model: nat ->bool),( mSsf model Gamma -> val model f = true).








(*Proof by Contradiction*)
Axiom pbc : forall (P: Prop), (~P -> False) -> P.
Axiom dnegE : forall P:Prop, (~~P->P).





(*Consistency:*)
(*Inductive Cons1 : Ensemble Formula -> Prop :=
|cons1 (Gamma: Ensemble Formula) (H:~(ND Gamma bot)): Cons1 Gamma.*)
Definition Cons (Gamma : Ensemble Formula) : Prop :=
~(ND Gamma bot).

Definition iCons (Gamma : Ensemble Formula) : Prop :=
(ND Gamma bot).



Lemma iConsEqiv : forall(Gamma : Ensemble Formula),
(exists f:Formula, In Formula Gamma f /\ In Formula Gamma (neg f))->iCons Gamma.
Proof. intros Gamma H. unfold iCons. destruct H. rename x into f.
apply negE with (f:=f). +apply ax. apply H.
+apply ax. apply H.
Qed.  


(*needed to prove the next lemma*)
Lemma about_Union: forall (A:Ensemble Formula)(f1 f2: Formula),
    Union Formula (Union Formula A (Singleton Formula f1)) (Singleton Formula  f2)=
    Union Formula (Union Formula A (Singleton Formula  f2)) (Singleton Formula f1).
    Proof. intros A f1 f2. rewrite ->Union_associative. 
    rewrite ->Union_commutative with (A:=(Singleton Formula f1)).
    rewrite ->Union_associative. reflexivity.  
Qed.

Lemma Weakening: forall(C:Ensemble Formula) (f1 f2:Formula), ND C f1 -> ND (Union Formula C (Singleton Formula f2)) f1.
Proof.
    intros C f1 f2 H. induction H.
    +apply ax. apply Union_introl. apply H.
    +apply conjE1 in IHND. apply IHND.
    +apply conjE2 in IHND. apply IHND.
    +apply conjI. -apply IHND1. -apply IHND2.
    +apply disjE with (C:=Union Formula C (Singleton Formula f2)) (f1:=f1) (f2:=f0).
        -rewrite ->about_Union. apply IHND1.
        -rewrite ->about_Union. apply IHND2.
        -apply IHND3.
    +apply disjI1. apply IHND.
    +apply disjI2. apply IHND.
    +apply impE with (f1:=f1) (f2:=f0).
        -apply IHND1. -apply IHND2.
    +apply impI. rewrite ->about_Union. apply IHND.
    +apply negE with(f:=f). -apply IHND1. -apply IHND2.
    +apply negI. rewrite ->about_Union. apply IHND.
    +apply botE. apply IHND.
    +apply RAA. rewrite ->about_Union. apply IHND.
    Qed. 

(*Lemma 1.4.5 (used in main proof!) *)
Lemma ConsSyns0: forall (Gamma:Ensemble Formula) (f:Formula),
iCons(Union Formula Gamma (Singleton Formula (neg f))) <-> ND Gamma f.
Proof.
    intros Gamma f.
    split.
    +intros H. unfold iCons in H. apply RAA in H. apply H.
    +intros H. unfold iCons. apply negE with (f:=f). -apply Weakening. apply H. 
        -apply ax. apply Union_intror. apply In_singleton.
    Qed.

Axiom contraposition : forall (P Q :Prop), (P <-> Q) -> (~P <-> ~Q).
Lemma ConsSyns: forall (Gamma:Ensemble Formula) (f:Formula),
~iCons(Union Formula Gamma (Singleton Formula (neg f))) <-> ~ND Gamma f.
Proof.
  intros Gamma f.
  apply contraposition. apply ConsSyns0.
  Qed.




(*/neat*)
(*Existence of Model:*)  
(*Zorn's Lemma:*)
Definition relation (U:Type) := U -> U -> Prop.
Definition reflexive (U:Type) (R : relation U) : Prop :=
    forall x:U, R x x.
Definition transitive (U:Type) (R : relation U) : Prop :=
    forall x y z:U, R x y->R y z -> R x z.
Definition symmetric (U:Type) (R : relation U) : Prop :=
    forall x y:U, R x y-> R y x.
Definition antisymmetric (U:Type) (R : relation U) : Prop :=
    forall x y:U, R x y-> R y x-> x=y.
Definition pao (U:Type) (R: relation U ) : Prop :=
    reflexive U R /\ transitive U R /\ antisymmetric U R.

(*Taghyir dadam!
Ye ensemble dge 
ezafe kardam.
Bazam taghyir!
shart pao boodane R
ezafe shod*)Definition chain (U:Type) (R: relation U) (S : Ensemble U) (T : Ensemble U)  : Prop :=
  pao U R /\ Included (U) T S /\(forall x y:U, In U T x -> In U T y -> (R x y \/ R y x)).

Definition maximal (U:Type) (S:Ensemble U) (x:U) (R:relation U) : Prop:=
    (forall y:U, In U S y -> R x y -> x=y) /\ In U S x.

Definition upper_bound (U:Type) (S:Ensemble U) (R: relation U) (T:Ensemble U) (ub:U): Prop:=
    (forall x:U, In U T x -> R x ub) /\ In U S ub.

Axiom Zorn's_Lemma: forall (U:Type) (S:Ensemble U) (R:relation U), 
    pao U R -> (forall (T: Ensemble U), (chain U R S T -> exists (s:U), upper_bound U S R T s) )
    -> exists (maxim:U), maximal U S maxim R .


(*Axiom Zorn's_Lemma: forall (U:Type) (S:Ensemble U) (R:relation U), 
    pao U R -> (forall (T: Ensemble U), (chain U R T -> exists (s:S), sup U R T s) )
    -> exists (maxim:U), maximal U maxim R.*)


(*max va sup ehtemalan niaz be tagheer daran!*)

(*Lemma 1.4.10:*)
Definition Inc : relation (Ensemble Formula) := Included Formula.

Definition TheSet(Gamma:Ensemble Formula) (Gammap:Ensemble Formula): Prop:=
    Inc Gamma Gammap /\ Cons Gammap.
Definition TheS(*name changed from S to TheS*) (Gamma : Ensemble Formula) : Ensemble (Ensemble Formula):= 
    TheSet Gamma.
(*Ta ChaharShanbe Ba Alireza Be in Residim!*)






(*Union of a Chain's Elements:*)


Definition PropUoCE (T: Ensemble (Ensemble Formula) ) (Gammap : Ensemble Formula) : Prop :=
forall (Gamma:Ensemble Formula),( In (Ensemble Formula) T Gamma ->
forall (f : Formula), (In Formula Gamma f-> In Formula Gammap f )).

Definition PropUoCE2 (T: Ensemble (Ensemble Formula) ) (f : Formula) : Prop :=
exists (Gamma:Ensemble Formula), (In (Ensemble Formula) T Gamma /\
In Formula Gamma f).

Definition UoCE1 (T: Ensemble (Ensemble Formula)) : Ensemble Formula :=
    PropUoCE2 T.  

Lemma About_PropUoCE : forall (f:Formula) (T:Ensemble (Ensemble Formula)), 
PropUoCE2 T f <-> In Formula (PropUoCE2 T) f.
Proof. intros f T. split. +intros H. apply H.
+intros H. unfold PropUoCE2. apply H. 
Qed.





(*Here!/*)

Lemma About_TheSet0 : forall (Gamma Gammap: (Ensemble Formula)),
TheSet Gamma Gammap->In (Ensemble Formula) (TheSet Gamma) Gammap.
Proof. intros Gamma Gammap H. apply H.
Qed.

Lemma About_TheSet : forall (Gamma Gammap: (Ensemble Formula)),
Inc Gamma Gammap /\ Cons Gammap->In (Ensemble Formula) (TheSet Gamma) Gammap.
Proof. intros Gamma Gammap H. apply About_TheSet0. unfold TheSet. apply H.
Qed. 

Lemma PropUoCE_Inclusion : forall (T : Ensemble (Ensemble Formula)) (Gamma : Ensemble Formula),
chain (Ensemble Formula) Inc (TheSet Gamma) T ->
(forall f:Formula, In Formula Gamma f -> PropUoCE2 T f) -> Inc Gamma (PropUoCE2 T).
Proof.
    intros T Gamma H H1 f H2. apply About_PropUoCE. apply H1. apply H2.
    Qed.

Lemma About_chain_in_TheSet : forall (T: Ensemble ( Ensemble Formula )) (Gamma Gamma': Ensemble Formula),
chain (Ensemble Formula) Inc (TheSet Gamma) T /\ In (Ensemble Formula) T Gamma' 
-> Cons Gamma'.
Proof. intros T Gamma Gamma' H. apply H. apply H.
Qed.

(*In axiom mesle ine ke kolan chain ha ro towri taarif konim
ke nonempty bashan. yaani intowr nist ke chize gheire badihi e ro 
asl begirim, mesle lemme zorn, balke engar ke darim be taarife
ye chizi ezafe mikonim*)
Axiom Chains_Are_Nonempty : forall (T: Ensemble (Ensemble Formula)) (Gamma:Ensemble Formula),
chain (Ensemble Formula) Inc (TheSet Gamma) T ->
exists Gamma':Ensemble Formula, In (Ensemble Formula) T Gamma'.
(*Before Here!
You are strugling!...*)

Lemma iConsEx : forall  (Gamma : Ensemble Formula),
iCons (Gamma) -> exists f:Formula,
ND Gamma f /\ ND Gamma (neg f).
Proof.
    intros Gamma H. unfold iCons in H. exists bot. split.
    +apply H. +apply negI. apply Weakening. apply H.
    Qed.





(*Fixpoint finite_set_creator (proof : Prop) : Ensemble Formula:=
    match proof with
    | ax Gamma f' (In Formula Gamma f') => Singleton Formula f end.
    *)
Theorem Compactness : forall (Gamma : Ensemble Formula) (f:Formula),
ND Gamma f -> (exists Gamma' : Ensemble Formula, 
Finite Formula Gamma' /\ ND Gamma' f /\ Inc Gamma' Gamma).
Proof. intros Gamma f H. (*Vase Esbatesh shayad oon mohmali ke
oon bala neveshti be karet biad.*) Admitted.




(*Pi'={f|(f in (union Es) ) st ( (E In T) /\ ) }*)



(*Definition The_Pi'_Prop_formula (T:Ensemble (Ensemble Formula)) (Gamma Pi : Ensemble Formula) (f:Formula) : Prop :=
    chain (Ensemble Formula) Inc (TheSet Gamma) T /\ Finite Formula Pi /\ Inc Pi (UoCE1 T) /\
    In Formula Pi f /\ exists Gamma':Ensemble Formula, In (Ensemble Formula) T Gamma.

Definition The_Pi'_Prop_ensemble (T:Ensemble (Ensemble Formula)) (Gamma Pi Pi' : Ensemble Formula) : Prop :=
    chain (Ensemble Formula) Inc (TheSet Gamma) T /\ Finite Formula Pi /\ Inc Pi (UoCE1 T) /\
    Inc Pi Pi' /\ In (Ensemble Formula) T Pi'.
*)

Definition min_chain_set (T:Ensemble (Ensemble Formula)) (Gamma min : Ensemble Formula) : Prop:=
    chain (Ensemble Formula) Inc (TheSet Gamma) T /\ forall (Pi : Ensemble Formula), In (Ensemble Formula) T Pi -> Inc min Pi. 

Definition min_chain_formula (T:Ensemble (Ensemble Formula)) (Gamma : Ensemble Formula) (f:Formula) : Prop:=
    chain (Ensemble Formula) Inc (TheSet Gamma) T /\ forall (Pi : Ensemble Formula), In (Ensemble Formula) T Pi -> In Formula Pi f.

Definition min_chain (T:Ensemble (Ensemble Formula)) (Gamma : Ensemble Formula) : Ensemble Formula :=
    min_chain_formula T Gamma.

Definition Includer_set (T:Ensemble (Ensemble Formula)) (Gamma : Ensemble Formula) (f : Formula) (Incl : Ensemble Formula) : Prop := 
    chain (Ensemble Formula) Inc (TheSet Gamma) T /\ In (Ensemble Formula) T Incl /\ In Formula Incl f.




Lemma UoCE1_has_subset : forall (T : Ensemble (Ensemble Formula)) (Gamma Pi: Ensemble Formula),
chain (Ensemble Formula) Inc (TheSet Gamma) T /\ Inc Pi (UoCE1 T) /\ Finite Formula Pi 
-> exists Pi', In (Ensemble Formula) T Pi' /\ Inc Pi Pi'.
Proof. intros T Gamma Pi H. Admitted.  



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
        intros H3. apply About_PropUoCE. unfold PropUoCE2.
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














(*Function in Lemma 1.4.11:*)

Definition Gamma_Max (Gamma Gammap : Ensemble Formula) : Prop :=
      









(*The Lemma:*)



Lemma Existence_of_Model: forall (Gamma : Ensemble Formula),
~iCons Gamma -> exists (model : nat -> bool), mSsf model Gamma. 
Proof. intros Gamma H. 



(*neat/*)
(*My own Lemma!*)
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


    



