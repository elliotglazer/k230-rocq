(** Actual proof operations for any unary source-axiom descriptor.  The
    internally finite axiom contexts explicitly contain only closed formulas;
    no axiom truth, completeness, or semantic satisfaction is assumed. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions NumericalTheories
  NumericalContexts NumericalEnvironments NumericalContextRenaming ContextCombination
  SetFormulaCodes SetCodeDescent SourceBounded SourceSequents SourceInstantiationConstructors
  SourceTraceBounds SourceClosedContextShift NumericalRenaming NumericalSourceFull
  SourceProofRenaming SourceProofWeakening SourceZFCGeneralization SourceClosedPrefixes
  NumericalSetClosure SourceAxiomContexts SourceDescriptorProvability.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Theorem source_descriptor_provable_definable M T :Definable1 M (source_descriptor_provable M T).
Proof.
  exists (source_descriptor_provable_formula T $0),(fun _=>zeroM M).
  intro f. symmetry. apply source_descriptor_provable_formula_correct.
Qed.

Theorem source_descriptor_provable_from_empty M T f :
  source_full_prv M (zeroM M) (zeroM M) (zeroM M) f ->source_descriptor_provable M T f.
Proof. intro HP. exists (zeroM M),(zeroM M),(zeroM M). split;[apply source_axiom_context_empty|exact HP]. Qed.

Theorem source_descriptor_provable_axiom M T f :
  theory_axiom M T f ->source_bounded M f (zeroM M) ->source_descriptor_provable M T f.
Proof.
  intros HA HB. destruct (environment_cons_total M (zeroM M) (zeroM M) (zeroM M) f)
    as (b&c&n&HC).
  assert (HBound:context_bounded M b c n (zeroM M)).
  { apply (proj2 (context_bounded_cons M _ _ _ f b c n (zeroM M) HC)).
    split;[exact HB|apply context_bounded_empty]. }
  exists b,c,n. split.
  - split;[exact HBound|]. intros g HG.
    apply (proj1 (context_member_cons M _ _ _ f b c n g HC)) in HG.
    destruct HG as [->|HG];[exact HA|exfalso;exact (context_empty M _ _ g HG)].
  - apply full_source_Ctx;[exists (zeroM M);auto|].
    apply (proj2 (context_member_cons M _ _ _ f b c n f HC)). now left.
Qed.

Theorem source_descriptor_provable_mp M T a d f :
  source_descriptor_provable M T a ->source_descriptor_provable M T f ->
  sf_relation M SFImpl a d f ->source_descriptor_provable M T d.
Proof.
  intros (ab&ac&an&HAC&HA) (fb&fc&fn&HFC&HF) HImpl.
  destruct (context_union_total M ab ac an fb fc fn) as (ub&uc&un&HU).
  pose proof (source_axiom_context_union M T ab ac an fb fc fn ub uc un HAC HFC HU) as HUC.
  pose proof (source_full_prv_weaken_bounded M ab ac an ub uc un a (zeroM M) HA
    (context_union_left M ab ac an fb fc fn ub uc un HU) (proj1 HUC)) as HA'.
  pose proof (source_full_prv_weaken_bounded M fb fc fn ub uc un f (zeroM M) HF
    (context_union_right M ab ac an fb fc fn ub uc un HU) (proj1 HUC)) as HF'.
  exists ub,uc,un. split;[exact HUC|].
  apply (full_source_IE M ub uc un a d f);[|exact HF'|exact HA'|exact HImpl].
  exact (source_wf_binary_right M ub uc un SFImpl a d f
    ltac:(unfold sf_binary;auto) HImpl (source_full_prv_wellformed M ub uc un f HF')).
Qed.

Theorem source_axiom_context_renaming M T b c n rb rc rn delta ub uc :
  source_axiom_context M T b c n ->context_renaming M b c n rb rc rn delta ub uc ->
  source_axiom_context M T ub uc n.
Proof.
  intros [HB HA] HR. pose proof (context_renaming_closed_members M b c n rb rc rn delta ub uc HB HR) as HMem.
  split;intros f HF;[apply HB|apply HA];exact (proj1 (HMem f) HF).
Qed.

Theorem source_descriptor_provable_renaming M T f rb rc rn delta g :
  source_descriptor_provable M T f ->numerical_renaming M f rb rc rn delta g ->
  source_descriptor_provable M T g.
Proof.
  intros (b&c&n&HC&HP) HR.
  destruct (context_renaming_total M b c n rb rc rn delta) as (ub&uc&HCR).
  exists ub,uc,n. split.
  - exact (source_axiom_context_renaming M T b c n rb rc rn delta ub uc HC HCR).
  - exact (source_full_prv_renaming M b c n f rb rc rn delta ub uc g HP HCR HR).
Qed.

Theorem source_descriptor_provable_all M T a f :
  source_descriptor_provable M T a ->sf_relation M SFAll a (zeroM M) f ->
  source_descriptor_provable M T f.
Proof.
  intros (b&c&n&HC&HP) HF. exists b,c,n. split;[exact HC|].
  exact (source_full_all_intro_closed M b c n a f (proj1 HC) HF HP).
Qed.

Theorem source_descriptor_provable_prefix_eliminate M T n body result :
  all_prefix M n body result ->source_descriptor_provable M T result ->
  source_descriptor_provable M T body.
Proof.
  intros HAll (b&c&l&HC&HP). exists b,c,l. split;[exact HC|].
  exact (source_full_prefix_eliminate M b c l n body result (proj1 HC) HAll HP).
Qed.

Print Assumptions source_descriptor_provable_definable.
Print Assumptions source_descriptor_provable_axiom.
Print Assumptions source_descriptor_provable_mp.
Print Assumptions source_descriptor_provable_renaming.
Print Assumptions source_descriptor_provable_all.
Print Assumptions source_descriptor_provable_prefix_eliminate.
