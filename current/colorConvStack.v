Require Import ThreeSatReduction.   

Theorem consApp : forall (A:Type) (hd:A) tl, hd::tl = [hd]++tl. auto. Qed. 
Theorem plus0 : forall n, n = n + 0. auto. Qed. 

Ltac negate H :=
  match type of H with
      |?x => assert(~ x)
  end. 

Theorem threeX : forall x, x+(x+(x+0)) = 3 * x + 0. auto. Qed. 

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

Theorem InTrueV : forall u c Gamma C i eta eta', 
                    setVertices Gamma C i eta' eta -> In (3*u,c) eta' -> 
                    In (u, true) eta -> c = u /\ c < C /\ In (3*u+1,C) eta'.
Proof.
  intros. induction H. 
  {destruct (eq_nat_dec u u0). 
   {tryInv; try (split;[auto|split;[omega|simpl;auto]]). omega. negate H1.
    rewrite (plus0 (3*u0)). eapply notInEta'; eauto. contradiction. omega.
    eapply IHsetVertices in H3; auto. invertHyp. split; auto. split. omega. simpl. 
    eauto. }  
   {tryInv; try omega; auto. eapply IHsetVertices in H1; eauto. invertHyp. split; auto.
    split. omega. simpl. auto. }
  }
  {destruct (eq_nat_dec u u0). 
   {tryInv; try omega; auto. negate H3. eapply notInEta; eauto. contradiction. 
    eapply IHsetVertices in H3; eauto. invertHyp. split; auto. split. omega. 
    simpl. auto. }
   {tryInv; try omega. apply IHsetVertices in H3; auto. invertHyp. split; auto. 
    split. omega. simpl. auto. }
  }
  {inv H0. }
Qed. 

Theorem InFalseV : forall u c Gamma C i eta eta', 
                    setVertices Gamma C i eta' eta -> In (3*u+1,c) eta' -> 
                    In (u, false) eta -> c = u /\ u < C /\ In (3*u,C) eta'.
Proof.
  intros. induction H. 
  {destruct (eq_nat_dec u u0). 
   {tryInv; try omega; auto. negate H3. eapply notInEta; eauto. contradiction. 
    eapply IHsetVertices in H3; eauto. invertHyp. split; auto. split. omega. 
    simpl. auto. }
   {tryInv; try omega. apply IHsetVertices in H3; auto. invertHyp. split; auto. 
    split. omega. simpl. auto. }
  }
  {destruct (eq_nat_dec u u0). 
   {tryInv; try (split;[auto|split;[omega|simpl;auto]]); try omega. negate H1.
    eapply notInEta'; eauto. contradiction. 
    eapply IHsetVertices in H3; auto. invertHyp. split; auto. }
   {tryInv; try omega; auto. eapply IHsetVertices in H1; eauto. invertHyp. split; auto.
    split. omega. simpl. auto. }
  }
  {inv H0. }
Qed. 

Theorem uniqueAppendNeq : forall (A:Type) S1 S2 (u1 u2:A) U,
                            In u1 S1 -> In u2 S2 -> unique U (S1 ++ S2) ->
                            u1 <> u2. 
Proof.
  induction S1; intros. 
  {inv H. }
  {inv H1. simpl in H. inv H. 
   {eapply uniqueNotIn in H4. Focus 2. apply Union_intror. constructor. 
    intros c. subst. apply H4. apply in_app_iff. auto. }
   {eauto. }
  }
Qed. 

Theorem uniqueMid : forall (A:Type) D1 D2 (u:A) U, 
                      unique U (D1++[u]++D2) ->
                      ~ In u (D1++D2). 
Proof.
  induction D1; intros. 
  {simpl in *. inv H. eapply uniqueNotIn. Focus 2. eauto. simpl. 
   apply Union_intror. constructor. }
  {inv H. rewrite consApp in H2. copy H2. eapply IHD1 in H2; eauto. simpl. 
   intros c. inv c. eapply uniqueNotIn in H. Focus 2. apply Union_intror. 
   constructor. apply H. rewrite in_app_iff. right. simpl. auto. contradiction. }
Qed. 

Theorem notInApp : forall (A:Type) D1 D2 (u u':A), ~ In u (D1++[u']++D2) ->
                                              ~ In u (D1++D2). 
Proof.
  intros. rewrite in_app_iff in *. intros c. apply H. inv c. auto. right.
  simpl. auto. 
Qed. 

Ltac invIn := 
  match goal with
      |H:In ?u (?x++?y) |- _ => rewrite in_app_iff in H; inv H; try invIn
  end. 

Ltac solveIn :=
  match goal with
      | |- In ?x (?a ++ ?b) => rewrite in_app_iff; 
                            solve[left; solveIn|right; solveIn]
      | |- In ?a ?b \/ In ?c ?d => simpl in *; solve[left; solveIn | right; solveIn]
      | |- In ?a (?b::?c) => simpl; solve[left; auto|right; solveIn]
      | |- _ => eauto
  end. 

Theorem TripleNotIn : forall (A:Type) (u1 u2 u3:A) U D1 D2 D3 D4, 
                        unique U (D1++u1::D2++u2::D3++u3::D4) ->
                        ~ In u1 (D1++D2++D3++D4) /\ ~ In u2 (D1++D2++D3++D4) /\
                        ~ In u3 (D1++D2++D3++D4). 
Proof.
  intros. assert(D1++u1::D2++u2::D3++u3::D4=D1++[u1]++(D2++u2::D3++u3::D4)). 
  auto. copy H. rewrite H0 in H. apply uniqueMid in H; eauto. 
  assert(D1++u1::D2++u2::D3++u3::D4=(D1++u1::D2)++[u2]++(D3++u3::D4)). 
  simpl. rewrite <- app_assoc. auto. copy H1. rewrite H2 in H1. 
  eapply uniqueMid in H1. 
  assert(D1++u1::D2++u2::D3++u3::D4=(D1++u1::D2++u2::D3)++[u3]++D4). simpl.
  rewrite <- app_assoc. simpl. rewrite <- app_assoc. auto. 
  rewrite H4 in H3. eapply uniqueMid in H3. split. intros c. apply H. 
  invIn; solveIn. split. intros c. apply H1. invIn; solveIn. intros c. 
  apply H3. invIn; solveIn. 
Qed. 

Theorem TripleNeq : forall (A:Type) (u1 u2 u3:A) U D1 D2 D3 D4, 
                      unique U (D1++u1::D2++u2::D3++u3::D4) ->
                      u1 <> u2 /\ u2 <> u3 /\ u1 <> u3. 
Proof.
  intros. assert(D1++u1::D2++u2::D3++u3::D4 = (D1++[u1]) ++ (D2++u2::D3++u3::D4)). 
  rewrite <- app_assoc. simpl. auto. copy H. rewrite H0 in H. 
  eapply uniqueAppendNeq in H. Focus 2. apply in_app_iff. right. simpl. eauto. 
  Focus 2. rewrite in_app_iff. simpl. right. left. auto. split. auto. 
  assert(D1++u1::D2++u2::D3++u3::D4 = (D1++u1::D2++u2::D3)++(u3::D4)). 
  repeat rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. auto. 
  copy H1. rewrite H2 in H1. eapply uniqueAppendNeq in H1. Focus 2.
  rewrite in_app_iff. right. simpl. right. rewrite in_app_iff. right. simpl. auto. 
  Focus 2. simpl. auto. split; auto.
  assert(D1++u1::D2++u2::D3++u3::D4 = (D1++[u1]) ++ (D2++u2::D3++u3::D4)). 
  rewrite <- app_assoc. auto. rewrite H4 in H3. eapply uniqueAppendNeq in H3. 
  Focus 2. rewrite in_app_iff. right. simpl. auto. Focus 2. rewrite in_app_iff. 
  simpl. right. right. rewrite in_app_iff. simpl. right. left. auto. auto. 
Qed. 

Theorem color_convert_base : forall Gamma Delta c u eta' eta'' G C eta, 
                               convert_base Gamma Delta c G ->
                               ~ In u Delta -> u < C ->
                               setVertices Gamma C 0 eta' eta -> 
                               coloring (eta'++(c,u)::eta'') G C. 
Proof.
  intros. induction H. 
  {constructor. }
  {eapply V_V'MapToUOrC in H; eauto. inv H. 
   {invertHyp. econstructor. solveIn. solveIn. omega. omega. intros c. subst. apply H0. 
    solveIn. econstructor. solveIn. solveIn. omega. omega. omega. apply IHconvert_base; auto. 
    intros c. apply H0. solveIn. }
   {invertHyp. econstructor. solveIn. solveIn. omega. omega. omega. econstructor. solveIn. 
    solveIn. omega. omega. intros c. apply H0. solveIn. apply IHconvert_base; auto. 
    intros c. apply H0. solveIn. }
  }
Qed. 

Theorem convFormulaColorable : forall i Gamma Delta G eta K U eta'' F eta' C, 
                                 setVertices Gamma C 0 eta' eta -> SAT' eta (F::K) ->
                                 setCs eta' i (F::K) eta'' eta -> 
                                 unique U Delta -> 
                                 convFormula i Gamma Delta F G -> coloring (eta'++eta'') G C.
Proof. 
  intros. inv H3. simpl. destruct e1. destruct e2. destruct e3. simpl in H2. 
  copy H2. apply TripleNeq in H2. invertHyp. copy H3.
  eapply TripleNotIn in H10. invertHyp. inv H1. 
  {inv H23.  
   {copy H. eapply InTrueV in H; eauto. invertHyp. subst. inv H8. copy H15.
    econstructor; try apply in_app_iff; simpl; eauto; try omega. inv H12. 
    {eapply V_V'MapToUOrC in H5; eauto. inv H5. 
     {invertHyp. econstructor. solveIn. solveIn. omega. auto. omega. copy H. 
      eapply V_V'MapToUOrC in H6; eauto. inv H6; invertHyp.  
      {inv H13; econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
      {inv H13; econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
     }
     {invertHyp. econstructor. solveIn. solveIn. omega. simpl in *. omega. auto. copy H6.
      eapply V_V'MapToUOrC in H6; eauto. inv H6; invertHyp. 
      {inv H13; econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
      {inv H13; econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
     }
    }
    {eapply V_V'MapToUOrC in H5; eauto. inv H5. 
     {invertHyp. econstructor. solveIn. solveIn. omega. simpl in *. omega. auto. 
      eapply V_V'MapToUOrC in H6; eauto. inv H6; invertHyp.  
      {inv H13; econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
      {inv H13; econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
     }
     {invertHyp. econstructor. solveIn. solveIn. omega. simpl in *. omega. omega. copy H6.
      eapply V_V'MapToUOrC in H6; eauto. inv H6; invertHyp. 
      {inv H13; econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
      {inv H13; econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
     }
    }
   }
   {copy H. eapply InFalseV in H; eauto. invertHyp. subst. inv H8. copy H15.
    econstructor; try apply in_app_iff; simpl; eauto; try omega. inv H12. 
    {eapply V_V'MapToUOrC in H5; eauto. inv H5. 
     {invertHyp. econstructor. solveIn. solveIn. omega. auto. omega. copy H. 
      eapply V_V'MapToUOrC in H6; eauto. inv H6; invertHyp.  
      {inv H13; econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
      {inv H13; econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
     }
     {invertHyp. econstructor. solveIn. solveIn. omega. simpl in *. omega. auto. copy H6.
      eapply V_V'MapToUOrC in H6; eauto. inv H6; invertHyp. 
      {inv H13; econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
      {inv H13; econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
     }
    }
    {eapply V_V'MapToUOrC in H5; eauto. inv H5. 
     {invertHyp. econstructor. solveIn. solveIn. omega. simpl in *. omega. auto. 
      eapply V_V'MapToUOrC in H6; eauto. inv H6; invertHyp.  
      {inv H13; econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
      {inv H13; econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
     }
     {invertHyp. econstructor. solveIn. solveIn. omega. simpl in *. omega. omega. copy H6.
      eapply V_V'MapToUOrC in H6; eauto. inv H6; invertHyp. 
      {inv H13; econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
      {inv H13; econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
     }
    }
   }
  }
  {inv H23.   
   {copy H. eapply InTrueV in H; eauto. invertHyp. subst.
    eapply V_V'MapToUOrC in H4; eauto. inv H4; invertHyp. 
    {inv H8; econstructor; try solveIn; try omega. 
     {inv H12; econstructor; try solveIn; try omega. 
      {eapply V_V'MapToUOrC in H6; eauto. inv H6; invertHyp.  
       {inv H13;econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
       {inv H13;econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
      }
     }
     {inv H12; econstructor; try solveIn; try omega. 
      {eapply V_V'MapToUOrC in H6; eauto. inv H6; invertHyp.  
       {inv H13; econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
       {inv H13; econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
      }
     }
    }
    {inv H8; econstructor; try solveIn; try omega. 
     {inv H12; econstructor; try solveIn; try omega. 
      {eapply V_V'MapToUOrC in H6; eauto. inv H6; invertHyp.  
       {inv H13; econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
       {inv H13; econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
      }
     }
     {inv H12; econstructor; try solveIn; try omega. 
      {eapply V_V'MapToUOrC in H6; eauto. inv H6; invertHyp.  
       {inv H13; econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
       {inv H13; econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
      }
     }
    }
   }
   {copy H. eapply InFalseV in H; eauto. invertHyp. subst.
    eapply V_V'MapToUOrC in H4; eauto. inv H4; invertHyp. 
    {inv H8; econstructor; try solveIn; try omega. 
     {inv H12; econstructor; try solveIn; try omega. 
      {eapply V_V'MapToUOrC in H6; eauto. inv H6; invertHyp.  
       {inv H13; econstructor; try solveIn; try omega; eapply color_convert_base; eauto.  }
       {inv H13; econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
      }
     }
     {inv H12; econstructor; try solveIn; try omega. 
      {eapply V_V'MapToUOrC in H6; eauto. inv H6; invertHyp.  
       {inv H13; econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
       {inv H13; econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
      }
     }
    }
    {inv H8; econstructor; try solveIn; try omega. 
     {inv H12; econstructor; try solveIn; try omega. 
      {eapply V_V'MapToUOrC in H6; eauto. inv H6; invertHyp.  
       {inv H13; econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
       {inv H13; econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
      }
     }
     {inv H12; econstructor; try solveIn; try omega. 
      {eapply V_V'MapToUOrC in H6; eauto. inv H6; invertHyp.  
       {inv H13; econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
       {inv H13; econstructor; try solveIn; try omega; eapply color_convert_base; eauto. }
      }
     }
    }
   } 
  }
  {inv H23.   
   {copy H. eapply InTrueV in H; eauto. invertHyp. subst.
    eapply V_V'MapToUOrC in H4; eauto. inv H4; invertHyp. 
    {inv H8; econstructor; try solveIn; try omega. 
     {eapply V_V'MapToUOrC in H5; eauto. inv H5; invertHyp. 
      {inv H12; econstructor; try solveIn; try omega. 
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
      }
      {inv H12; econstructor; try solveIn; try omega. 
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
      }
     }
     {eapply V_V'MapToUOrC in H5; eauto. inv H5; invertHyp. 
      {inv H12; econstructor; try solveIn; try omega. 
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
      }
      {inv H12; econstructor; try solveIn; try omega. 
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
      }
     }
    }
    {inv H8; econstructor; try solveIn; try omega. 
     {eapply V_V'MapToUOrC in H5; eauto. inv H5; invertHyp. 
      {inv H12; econstructor; try solveIn; try omega. 
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
      }
      {inv H12; econstructor; try solveIn; try omega. 
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
      }
     }
     {eapply V_V'MapToUOrC in H5; eauto. inv H5; invertHyp. 
      {inv H12; econstructor; try solveIn; try omega. 
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
      }
      {inv H12; econstructor; try solveIn; try omega. 
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
      }
     }
    }
   }
   {copy H. eapply InFalseV in H; eauto. invertHyp. subst.
    eapply V_V'MapToUOrC in H4; eauto. inv H4; invertHyp. 
    {inv H8; econstructor; try solveIn; try omega. 
     {eapply V_V'MapToUOrC in H5; eauto. inv H5; invertHyp. 
      {inv H12; econstructor; try solveIn; try omega. 
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
      }
      {inv H12; econstructor; try solveIn; try omega. 
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
      }
     }
     {eapply V_V'MapToUOrC in H5; eauto. inv H5; invertHyp. 
      {inv H12; econstructor; try solveIn; try omega. 
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
      }
      {inv H12; econstructor; try solveIn; try omega. 
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
      }
     }
    }
    {inv H8; econstructor; try solveIn; try omega. 
     {eapply V_V'MapToUOrC in H5; eauto. inv H5; invertHyp. 
      {inv H12; econstructor; try solveIn; try omega. 
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
      }
      {inv H12; econstructor; try solveIn; try omega. 
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
      }
     }
     {eapply V_V'MapToUOrC in H5; eauto. inv H5; invertHyp. 
      {inv H12; econstructor; try solveIn; try omega. 
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
      }
      {inv H12; econstructor; try solveIn; try omega. 
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
       {inv H13; econstructor; try solveIn; try omega;eapply color_convert_base; eauto. }
      }
     }
    }
   }
  }
Qed. 

Theorem convStackColorable : forall i Gamma Delta G eta F U eta'' eta' C, 
                               setVertices Gamma C 0 eta' eta -> SAT' eta F ->
                               setCs eta' i F eta'' eta ->
                               unique U Delta -> 
                               convStack i Gamma Delta F G -> coloring (eta' ++ eta'') G C.
Proof.
  intros. genDeps {{ U; eta; eta'; C; eta'' }}. induction H3; intros. 
  {constructor. }
  {constructor. 
   {inv H1. inv H2. 
    {rewrite consApp. apply colorWeakeningApp. eapply IHconvStack; eauto. 
     rewrite plus_comm. auto. }
    {rewrite consApp. apply colorWeakeningApp. eapply IHconvStack; eauto.
     rewrite plus_comm. auto. }
    {rewrite consApp. apply colorWeakeningApp. eapply IHconvStack; eauto.
     rewrite plus_comm. auto. }
   }
   {eapply convFormulaColorable; eauto. }
  }
Qed. 






  

























