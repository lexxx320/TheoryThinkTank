Require Import ThreeSatReduction.   




Theorem convertBaseColorable : forall i Gamma Delta G F eta S5 eta'' eta' C, 
                                 setVertices Gamma C 0 eta' eta -> 
                                 setCs eta' (3 * length Gamma) F eta'' eta -> 
                                 genericUnique S5 (fun x => x) Delta -> 
                                 convert_base Gamma Delta i G -> coloring eta' G C.
Admitted. 

Theorem colorWeakeningApp : forall eta1 eta2 eta3 G C,
                           coloring (eta1++eta3) G C ->
                           coloring (eta1++eta2++eta3) G C. 
Proof.
  intros. genDeps {{ eta2 }}. remember(eta1++eta3). induction H; intros. 
  {constructor. }
  {subst. econstructor. apply in_app_iff in H. inv H. auto. apply in_app_iff; simpl.
   eauto. repeat rewrite in_app_iff. auto. apply in_app_iff in H0. inv H0; 
   repeat rewrite in_app_iff; eauto. auto. auto. auto. eapply IHcoloring; eauto. }
  {constructor; eauto. }
Qed. 

Theorem consApp : forall (A:Type) (hd:A) tl, hd::tl = [hd]++tl. auto. Qed. 
Theorem plus0 : forall n, n = n + 0. auto. Qed. 

Ltac negate H :=
  match type of H with
      |?x => assert(~ x)
  end. 

Theorem InEtaInEta' : forall u c b Gamma C i eta eta', In (u, b) eta -> In (3*u, c) eta' -> 
                                            setVertices Gamma C i eta' eta -> 
                                            (c = u /\ In (u, true) eta) \/ (c = C /\ In (u, false) eta). 
Proof.
  intros. genDeps {{ u; c; b }}. induction H1; intros. 
  {destruct (eq_nat_dec u u0). 
   {subst. inCons. invertTupEq. left. split; simpl; auto. inCons. invertTupEq. omega. 
    inCons. invertTupEq. omega. negate H3. assert(3*u0=3*u0+0) by auto. rewrite H2. 
    eapply notInEta'; eauto. contradiction. }
   {inCons. invertTupEq. omega. inCons. invertTupEq. omega. inCons. invertTupEq. 
    omega. inCons. invertTupEq. omega. eapply IHsetVertices in H3; eauto. inv H3. invertHyp. 
    left. split; simpl; auto. invertHyp. right. split; simpl; auto. }
  }
  {destruct (eq_nat_dec u u0). 
   {subst. inCons. invertTupEq. right. split; simpl; auto. inCons. invertTupEq. omega. 
    inCons. invertTupEq. omega. negate H3. assert(3*u0=3*u0+0) by auto. rewrite H2. 
    eapply notInEta'; eauto. contradiction. }
   {inCons. invertTupEq. omega. inCons. invertTupEq. omega. inCons. invertTupEq. 
    omega. inCons. invertTupEq. omega. eapply IHsetVertices in H3; eauto. inv H3. invertHyp. 
    left. split; simpl; auto. invertHyp. right. split; simpl; auto. }
  }
  {inv H. }
Qed. 

Theorem threeX : forall x, x+(x+(x+0)) = 3 * x + 0. auto. Qed. 

Theorem helper : forall Gamma C p1 eta eta' i c G u eta'' v v0 u', 
              u = getVar p1 -> setVertices Gamma C 0 eta' eta -> In (u,3*u,3*u+1,3*u+2) Gamma -> winner eta p1 u' ->
              mkEdge i p1 (3*u) (3*u+1) (v,v0) -> In (3 * u', c) eta' -> 
              coloring(eta' ++ (i,c)::eta'') G C ->
              coloring(eta' ++ (i,c)::eta'') (newEdge v v0 G) C.
Proof.
  intros. inversion H3; subst. 
  {inv H2. 
   {copy H1. eapply V_V'MapToUOrC in H1; eauto. inv H1. 
    {invertHyp. simpl in *. 
Admitted. 

Ltac tryInv := repeat (try inCons; try invertTupEq). 

Theorem notInEta : forall Gamma C i c eta' epsilon eta u, setVertices Gamma C i eta' eta -> u < i -> 
                                     epsilon = 0 \/ epsilon = 1 \/ epsilon = 2 -> ~ In (u, c) eta. 
Proof.
  intros. induction H. 
  {intros contra. simpl in *. inv contra. 
   {invertTupEq. omega. }
   {assert(u < S u0). omega. apply IHsetVertices in H4. contradiction. }
  }
  {intros contra. simpl in *. inv contra. 
   {tryInv. omega. }
   {assert(u < S u0). omega. apply IHsetVertices in H4. contradiction. }
  }
  {intros contra. inv contra. }
Qed. 



Theorem InTrueV : forall u c Gamma C i eta eta', setVertices Gamma C i eta' eta ->
                                      In (3*u,c) eta' -> In (u, true) eta -> c = u /\ c < C.
Proof.
  intros. induction H. 
  {destruct (eq_nat_dec u u0). 
   {tryInv; try omega; auto. negate H1. rewrite (plus0 (3*u0)).
    eapply notInEta'; eauto. contradiction. }
   {tryInv; try omega; auto. }
  }
  {destruct (eq_nat_dec u u0). 
   {tryInv; try omega; auto. negate H3. eapply notInEta; eauto. contradiction. }
   {tryInv; try omega. auto. }
  }
  {inv H0. }
Qed. 

Theorem InTrueV' : forall u Gamma C i eta eta', setVertices Gamma C i eta' eta ->
                                       In (u, true) eta -> In (3*u+1, C) eta'.
Proof.
  intros. induction H. 
  {destruct (eq_nat_dec u u0). 
   {tryInv; simpl;auto. }
   {tryInv. omega. apply IHsetVertices in H2. simpl. eauto. }
  }
  {destruct (eq_nat_dec u u0). 
   {tryInv; simpl;auto. }
   {tryInv. apply IHsetVertices in H2. simpl. eauto. }
  }
  {inv H0. }
Qed. 

Theorem uniqueAppendNeq : forall (A:Type) S1 S2 (u1 u2:A) U,
                            In u1 S1 -> In u2 S2 -> genericUnique U (fun x => x) (S1 ++ S2) ->
                            u1 <> u2. 
Proof.
  induction S1; intros. 
  {inv H. }
  {inv H1. simpl in H. inv H. 
   {eapply genericUniqueNotIn in H4. Focus 2. apply Union_intror. constructor. 
    intros c. subst. apply H4. apply in_app_iff. auto. }
   {eauto. }
  }
Qed. 

Theorem TripleNeq : forall (A:Type) (u1 u2 u3:A) U D1 D2 D3 D4, 
                      genericUnique U (fun x => x) (D1++u1::D2++u2::D3++u3::D4) ->
                      u1 <> u2 /\ u2 <> u3 /\ u1 <> u3. 
Proof.
  intros. assert(D1++u1::D2++u2::D3++u3::D4 = (D1++[u1]) ++ (D2++u2::D3++u3::D4)). 
  rewrite <- app_assoc. simpl. auto. copy H. rewrite H0 in H. eapply uniqueAppendNeq in H. 
  Focus 2. apply in_app_iff. right. simpl. eauto. Focus 2. rewrite in_app_iff. 
  simpl. right. left. auto. split. auto. 
  assert(D1++u1::D2++u2::D3++u3::D4 = (D1++u1::D2++u2::D3)++(u3::D4)). 
  repeat rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. auto. 
  copy H1. rewrite H2 in H1. eapply uniqueAppendNeq in H1. Focus 2. rewrite in_app_iff. 
  right. simpl. right. rewrite in_app_iff. right. simpl. auto. Focus 2. simpl. auto. 
  split; auto. assert(D1++u1::D2++u2::D3++u3::D4 = (D1++[u1]) ++ (D2++u2::D3++u3::D4)). 
  rewrite <- app_assoc. auto. rewrite H4 in H3. eapply uniqueAppendNeq in H3. Focus 2. 
  rewrite in_app_iff. right. simpl. auto. Focus 2. rewrite in_app_iff. simpl. 
  right. right. rewrite in_app_iff. simpl. right. left. auto. auto. 
Qed. 

Ltac solveIn :=
  match goal with
      | |- In ?x (?a ++ ?b) => rewrite in_app_iff; simpl; solve[left; solveIn|right; solveIn]
      | |- In ?a ?b \/ In ?c ?d => solve[left; solveIn | right; solveIn]
      | |- _ => eauto
  end. 

Theorem convFormulaColorable : forall i Gamma Delta G eta K U eta'' F eta' C, 
                                 setVertices Gamma C 0 eta' eta -> SAT' eta (F::K) ->
                                 setCs eta' i (F::K) eta'' eta -> 
                                 genericUnique U (fun x => x) Delta -> 
                                 convFormula i Gamma Delta F G -> coloring (eta'++eta'') G C.
Proof. 
  intros. inv H3. simpl. destruct e1. destruct e2. destruct e3. simpl in H2. 
  copy H2. apply TripleNeq in H2. invertHyp. inv H1.  
  {inv H21. 
   {copy H. eapply InTrueV in H; eauto. invertHyp. subst. inv H8. copy H10.
    eapply InTrueV' in H10; eauto. econstructor; try apply in_app_iff; simpl; eauto; try omega.  
    inv H12. 
    {eapply V_V'MapToUOrC in H5; eauto. inv H5. 
     {invertHyp. econstructor. solveIn. solveIn. omega. auto. omega. copy H. 
      eapply V_V'MapToUOrC in H6; eauto. inv H6; invertHyp. 
      {inv H13; econstructor; try solveIn; try omega. 


admit. admit. }
      {inv H13; econstructor; try solveIn; try omega. admit. admit. }
     }
      

 copy H. eapply InNeq in H; eauto. invertHyp. econstructor. apply in_app_iff.
     simpl. auto. apply in_app_iff. simpl. eauto. auto. auto. auto. 
     inv H12. 


inversion H8; subst. 
    {inversion H12; subst.  
     {inversion H13; subst. 
      {inv H18. copy H3. eapply InEtaInEta' in H1; eauto. inv H1. invertHyp. 
       eapply 

simpl in *. 
    {eapply helper; eauto. simpl. eauto. eapply helper; eauto. simpl. eauto. simpl.
     



inv H18.  
     {copy H4. eapply V_V'MapToUOrC in H4; try eassumption. inv H4. 
      {invertHyp. inv H0. eapply lookupEta'Det in H17; eauto. subst. econstructor. 
       apply in_app_iff. simpl. right. eauto. apply in_app_iff. left. eauto. omega. 
       auto. omega. 


 copy H3. eapply InEtaInEta' in H3; eauto. inv H3. 
       {invertHyp. econstructor. apply in_app_iff. right. simpl. eauto. apply in_app_iff. 
        left. eauto. 

Focus 2. 
       invertHyp. econstructor. apply in_app_iff. right. simpl. eauto. apply in_app_iff.
       left. eauto. auto. omega. omega. omega. 



Theorem A : forall Gamma u C eta eta', 
              setVertices Gamma C 0 eta' eta -> In (u,3*u,3*u+1,3*u+2) Gamma ->
              coloring

Theorem convStackColorable : forall i Gamma Delta G eta F j S5 eta'' eta' C, 
                               setVertices Gamma C 0 eta' eta -> 
                               setCs eta' j F eta'' eta ->
                               genericUnique S5 (fun x => x) Delta -> 
                               convStack i Gamma Delta F G -> coloring (eta' ++ eta'') G C.
Proof.
  intros. genDeps {{ S5; eta; eta'; C; eta''; j }}. induction H2; intros. 
  {constructor. }
  {constructor. 
   {inv H1. 
    {rewrite consApp. apply colorWeakeningApp. eapply IHconvStack; eauto. }
    {rewrite consApp. apply colorWeakeningApp. eapply IHconvStack; eauto. }
    {rewrite consApp. apply colorWeakeningApp. eapply IHconvStack; eauto. }
   }
   {eapply convFormulaColorable; eauto. }
  }
Qed. 






  



























ad;lfkhjasdf

