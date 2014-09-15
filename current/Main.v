Require Import cliqueColorable.    

Theorem validEnvDomainUnique : forall Gamma C eta' eta i U, 
                                 valid Gamma C i eta' eta ->
                                 (forall x, Ensembles.In _ U x -> x > 3 * i + 2) -> 
                                 genericUnique U (fun a => match a with (x,y) => x end) eta'. 
Proof.
  intros. genDeps {{ U }}. induction H; intros. 
  {constructor. constructor. constructor. eapply IHvalid. intros. inv H3.
   inv H4. inv H1. apply H2 in H3. omega. inv H3. omega. inv H1. omega. inv H4. omega.
   intros c. inv c. inv H3. apply H2 in H1. omega. inv H1. omega. inv H3. omega. 
   intros c. inv c. apply H2 in H3. omega. inv H3. omega. intros c. apply H2 in c. omega. }
  {constructor. constructor. constructor. eapply IHvalid. intros. inv H3.
   inv H4. inv H1. apply H2 in H3. omega. inv H3. omega. inv H1. omega. inv H4. omega.
   intros c. inv c. inv H3. apply H2 in H1. omega. inv H1. omega. inv H3. omega. 
   intros c. inv c. apply H2 in H3. omega. inv H3. omega. intros c. apply H2 in c. omega. }
  {constructor. }
Qed. 

Theorem KColorNPC : forall Gamma Delta F C eta G eta' S1 S2 S3 S4 U,
                      reduce Gamma Delta F C G -> uniqueLockstep S1 S2 S3 S4 Gamma ->
                      valid Gamma C 1 eta' eta -> genericUnique U (fun x => x) Delta -> 
                      (SAT' eta F <-> coloring eta' G C).
Proof. 
  intros. inv H. split; intros. 
  {constructor. admit. constructor. copy H1. 
   apply validEnvDomainUnique with (U:=Empty_set _) in H1. Focus 2. intros. 
   inv H7. eapply cliqueColorable; eauto. admit. }
  {Admitted. 


Theorem buildCtxtUnique : forall n Gamma Delta U, 
                            (Gamma, Delta) = buildCtxt n -> 
                            (forall x, Ensembles.In vvar U x -> x > n) -> 
                            genericUnique U (fun x=> x) Delta. 
Proof.
  induction n; intros. 
  {simpl in *. inv H. constructor. }
  {simpl in *. destruct (buildCtxt n). invertTupEq. constructor.
   eapply IHn; eauto. intros. inv H. apply H0 in H1. omega. inv H1. omega. 
   intros c. apply H0 in c. omega. }
Qed. 

Theorem buildCtxtUniqueLS : forall n Gamma Delta S1 S2 S3 S4, 
                              (Gamma, Delta) = buildCtxt n -> 
                              (forall x, Ensembles.In vvar S1 x -> x > n) ->
                              (forall x, Ensembles.In vvar S2 x -> x > 3*n) ->
                              (forall x, Ensembles.In vvar S3 x -> x > 3*n+1) ->
                              (forall x, Ensembles.In vvar S4 x -> x > 3*n+2) ->
                              uniqueLockstep S1 S2 S3 S4 Gamma.
Proof.
  induction n; intros. 
  {simpl in *. invertTupEq. repeat econstructor. }
  {simpl in *. destruct (buildCtxt n) eqn:eq. invertTupEq. constructor. 
   eapply IHn; auto. intros; inv H;[apply H0 in H4; omega|inv H4;omega].
   intros; inv H; [apply H1 in H4; omega|inv H4;omega].  
   intros; inv H;[apply H2 in H4; omega|inv H4;omega]. 
   intros; inv H;[apply H3 in H4; omega|inv H4;omega]. 
   intros c. apply H0 in c. omega. intros c. apply H1 in c. omega. intros c. 
   apply H2 in c. omega. intros c. apply H3 in c. omega. }
Qed. 

Theorem KColorNPCTopLevel : forall Gamma Delta F n G eta eta', 
                              (Gamma, Delta) = buildCtxt n ->
                              reduce Gamma Delta F (n+1) G -> valid Gamma (n+1) 1 eta' eta ->
                              (SAT' eta F <-> coloring eta' G (n+1)). 
Proof.
  intros. copy H. apply buildCtxtUnique with (U:=Empty_set _) in H. Focus 2. intros. 
  inv H3. eapply buildCtxtUniqueLS with (S1:=Empty_set _)(S2:=Empty_set _)
          (S3:=Empty_set _)(S4:=Empty_set _) in H2; try solve[intros c1 c2; inv c2].
  eapply KColorNPC in H0; eauto. 
Qed. 


