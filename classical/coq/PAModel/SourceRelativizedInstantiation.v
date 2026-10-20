(** Source-to-source quantifier instantiation. The D(t) premise below is
    an ordinary proof in the target source calculus, not a transfer axiom. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts SourceSequents NumericalSourceFull NumericalInstantiation
  SourceRelativizationRules SourceRelativization SourceRelativizationFunctionality
  SourceRelativizationBounds SourceRelativizationInstances SourceInstantiationConstructors.
Unset Implicit Arguments.

Theorem source_relativized_AllE M domain a f t g rf rg dt b c n :
  source_bounded M domain (code_numeral M 1) ->
  sf_relation M SFAll a (zeroM M) f -> numerical_instantiation M a t g ->
  source_relativization M domain f rf -> source_relativization M domain g rg ->
  numerical_instantiation M domain t dt ->
  source_full_prv M b c n rf -> source_full_prv M b c n dt ->
  source_full_prv M b c n rg.
Proof.
  intros HD HF HG HRF HRG HDT PF PDT.
  destruct (source_relativization_quantifier_inv M domain true a f rf HF HRF)
    as [body [HBody [mid [HMid HAll]]]].
  destruct (source_relativization_instantiation_exists M domain a body t g HD HBody HG)
    as [inst [HInst HSub]].
  pose proof (source_relativization_functional M g domain inst rg HInst HRG) as E.
  subst inst.
  destruct (sf_relation_total M SFImpl dt rg) as [imp HImp].
  assert (HSubMid:numerical_instantiation M mid t imp).
  { exact (source_instantiation_binary M SFImpl domain body mid t dt rg imp
      (or_intror (or_intror eq_refl)) HMid HDT HSub HImp). }
  assert (HWF:source_sequent_wf M b c n imp).
  { exact (source_wf_quantifier_instance M b c n SFAll mid rf t imp
      (or_introl eq_refl) HAll (source_full_prv_wellformed M b c n rf PF) HSubMid). }
  apply (full_source_IE M b c n dt rg imp).
  - exact (source_wf_binary_right M b c n SFImpl dt rg imp
      (or_intror (or_intror eq_refl)) HImp HWF).
  - exact (full_source_AllE M b c n mid rf t imp HWF PF HAll HSubMid).
  - exact PDT.
  - exact HImp.
Qed.

Theorem source_relativized_ExI_wf M domain a f t g rf rg dt b c n :
  source_bounded M domain (code_numeral M 1) ->
  sf_relation M SFEx a (zeroM M) f -> numerical_instantiation M a t g ->
  source_relativization M domain f rf -> source_relativization M domain g rg ->
  numerical_instantiation M domain t dt ->
  source_sequent_wf M b c n rf ->
  source_full_prv M b c n rg -> source_full_prv M b c n dt ->
  source_full_prv M b c n rf.
Proof.
  intros HD HF HG HRF HRG HDT HWF PG PDT.
  destruct (source_relativization_quantifier_inv M domain false a f rf HF HRF)
    as [body [HBody [mid [HMid HEx]]]].
  destruct (source_relativization_instantiation_exists M domain a body t g HD HBody HG)
    as [inst [HInst HSub]].
  pose proof (source_relativization_functional M g domain inst rg HInst HRG) as E.
  subst inst.
  destruct (sf_relation_total M SFAnd dt rg) as [conj HConj].
  assert (HSubMid:numerical_instantiation M mid t conj).
  { exact (source_instantiation_binary M SFAnd domain body mid t dt rg conj
      (or_introl eq_refl) HMid HDT HSub HConj). }
  assert (HWFConj:source_sequent_wf M b c n conj).
  { exact (source_wf_binary M b c n SFAnd dt rg conj (or_introl eq_refl) HConj
      (source_full_prv_wellformed M b c n dt PDT)
      (source_full_prv_wellformed M b c n rg PG)). }
  apply (full_source_ExI M b c n mid rf t conj HWF).
  - exact (full_source_CI M b c n dt rg conj HWFConj PDT PG HConj).
  - exact HEx.
  - exact HSubMid.
Qed.

Theorem source_relativized_ExI M domain a f t g rf rg dt b c n k :
  source_bounded M domain (code_numeral M 1) ->
  source_bounded M f k -> context_bounded M b c n k ->
  sf_relation M SFEx a (zeroM M) f -> numerical_instantiation M a t g ->
  source_relativization M domain f rf -> source_relativization M domain g rg ->
  numerical_instantiation M domain t dt ->
  source_full_prv M b c n rg -> source_full_prv M b c n dt ->
  source_full_prv M b c n rf.
Proof.
  intros HD HB HC HF HG HRF HRG HDT PG PDT.
  apply (source_relativized_ExI_wf M domain a f t g rf rg dt b c n
    HD HF HG HRF HRG HDT);try assumption.
  exists k. split;[|exact HC].
  exact (source_relativization_preserves_bound M f domain k rf HD HB HRF).
Qed.

Print Assumptions source_relativized_AllE.
Print Assumptions source_relativized_ExI_wf.
Print Assumptions source_relativized_ExI.
