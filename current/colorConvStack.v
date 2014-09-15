Require Import ThreeSatReduction. 

Theorem convFormulaColorable : forall i Gamma Delta G F eta U S1 S2 S3 S4 S5 eta' C, 
                                 valid Gamma C 1 eta' eta -> 
                                 uniqueLockstep S1 S2 S3 S4 Gamma ->
                                 genericUnique S5 (fun x => x) Delta -> 
                                 genericUnique U (fun a=>match a with (x,y) => x end) eta' ->
                                 convFormula i Gamma Delta F G -> coloring eta' G C.
Proof. 
  intros. inv H3. simpl. destruct e1. destruct e2. destruct e3. 
  
Theorem convertBaseColorable : forall i Gamma Delta G F eta U S1 S2 S3 S4 S5 eta' C, 
                                 valid Gamma C 1 eta' eta -> 
                                 uniqueLockstep S1 S2 S3 S4 Gamma ->
                                 genericUnique S5 (fun x => x) Delta -> 
                                 genericUnique U (fun a=>match a with (x,y) => x end) eta' ->
                                 convert_base Gamma Delta i G -> coloring eta' G C.






Theorem convStackColorable : forall i Gamma Delta K G eta U S1 S2 S3 S4 S5 eta' C, 
                               valid Gamma C 1 eta' eta -> 
                               uniqueLockstep S1 S2 S3 S4 Gamma ->
                               genericUnique S5 (fun x => x) Delta -> 
                               genericUnique U (fun a=>match a with (x,y) => x end) eta' ->
                               convStack i Gamma Delta K G -> coloring eta' G C.
Proof.
  intros. genDeps {{ U; S1; S2; S3; S4; S5; eta; eta'; C }}. induction H3; intros. 
  {constructor. }
  {constructor. eapply IHconvStack; eauto. eapply convFormulaColorable; eauto. }
Qed. 


