Require Import cliqueColorable.      
Require Import colorVarsToClique. 
Require Import colorConvStack. 
Require Import colorImpliesSAT. 

Ltac inSet :=
  match goal with
      |H:Ensembles.In _ (Add _ ?x ?y) ?z |- _ => inv H
      |H:Ensembles.In _ (Singleton _ ?x) ?y |- _ => inv H
  end. 

Theorem KColorNPC : forall Gamma Delta F C eta G eta' U,
                      reduce Gamma Delta F C G -> 
                      valid Gamma C F eta' eta -> unique U Delta -> 
                      (SAT' eta F <-> coloring eta' G C).
Proof. 
  intros. inv H. split; intros. 
  {constructor. 
   {inv H0. eapply convStackColorable in H2; eauto. rewrite mult_comm. auto. }
   {constructor. 
    {inv H0. eapply colorWeakening. eapply cliqueColorable; eauto. }
    {inv H0. apply colorWeakening. eapply varsToCliqueColorable; eauto. }
   }
  }
  {inv H0. inv H. inv H11. eapply colorImpliesSAT. eauto. eauto. eapply H9.
   auto. eauto. rewrite mult_comm. eauto. }
Qed. 

Theorem buildCtxtUnique : forall i n Gamma Delta U, 
                            buildCtxt n i Gamma Delta -> 
                            (forall x, Ensembles.In vvar U x -> x < i) -> 
                            unique U Delta. 
Proof.
  intros. generalize dependent U. induction H; intros. 
  {constructor. eapply IHbuildCtxt. intros. inSet. apply H0 in H2. 
   auto. inSet. omega. intros c. apply H0 in c. omega. }
  {constructor. }
Qed. 

Theorem KColorNPCTopLevel : forall Gamma Delta F n G eta eta', 
                              buildCtxt n 0 Gamma Delta ->
                              reduce Gamma Delta F (n+1) G -> valid Gamma (n+1) F eta' eta ->
                              (SAT' eta F <-> coloring eta' G (n+1)). 
Proof.
  intros. apply buildCtxtUnique with (U:=Empty_set _) in H. Focus 2. intros. 
  inv H2. eapply KColorNPC in H0; eauto. 
Qed. 


