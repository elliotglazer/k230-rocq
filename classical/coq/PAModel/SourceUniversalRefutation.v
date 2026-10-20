(** A quantified assumption whose chosen instance contradicts two actual
    source ZFC theorems implies any wellformed conclusion.  The two theorem
    contexts are combined and weakened by the checked internal operations. *)
From PAModel Require Import Model FiniteCoding FiniteCRT SetFormulaCodes SetCodeDescent
  SourceBounded NumericalContexts NumericalEnvironments ContextCombination
  SourceSequents SourceTraceBounds SourceContextTransport SourceInstantiationConstructors
  NumericalInstantiation NumericalSourceFull SourceProofWeakening
  SourceZFCProvability SourceZFCBasicClosure.
Unset Implicit Arguments.

Theorem source_zfc_universal_refutation M eq bad neg matrix quantified instance witness goal out :
  source_zfc_provable M eq -> source_zfc_provable M neg ->
  sf_relation M SFImpl bad (zeroM M) neg ->
  sf_relation M SFAll matrix (zeroM M) quantified ->
  numerical_instantiation M matrix witness instance ->
  sf_relation M SFImpl eq bad instance ->
  sf_relation M SFImpl quantified goal out ->
  source_sequent_wf M (zeroM M) (zeroM M) (zeroM M) out ->
  source_zfc_provable M out.
Proof.
  intros (eb&ec&en&HEC&HE) (nb&nc&nn&HNC&HN) HNeg HQ HInst HI HO HWO.
  destruct (context_union_total M eb ec en nb nc nn) as (ub&uc&un&HU).
  pose proof (source_zfc_context_union M eb ec en nb nc nn ub uc un HEC HNC HU) as HUC.
  pose proof (source_zfc_context_closed M ub uc un HUC) as HUB.
  pose proof (source_wf_binary_left M (zeroM M) (zeroM M) (zeroM M)
    SFImpl quantified goal out ltac:(unfold sf_binary;auto) HO HWO) as HWQ.
  destruct (environment_cons_total M ub uc un quantified) as (db&dc&dn&HC).
  assert (HDB:source_context_finite_bound M db dc dn).
  { apply (source_context_finite_bound_cons M ub uc un quantified db dc dn
      (ex_intro _ (zeroM M) HUB));[|exact HC].
    destruct HWQ as [k [HK _]]. exists k. exact HK. }
  destruct HDB as [bound HBound].
  assert (HWQ':source_sequent_wf M db dc dn quantified).
  { exact (source_wf_transport_context M _ _ _ quantified db dc dn HWQ (ex_intro _ bound HBound)). }
  assert (HPQ:source_full_prv M db dc dn quantified).
  { apply full_source_Ctx;[exact HWQ'|].
    apply (proj2 (context_member_cons M ub uc un quantified db dc dn quantified HC)). now left. }
  assert (HE':source_full_prv M db dc dn eq).
  { apply (source_full_prv_weaken_bounded M eb ec en db dc dn eq bound HE);[|exact HBound].
    intros f HF. apply (proj2 (context_member_cons M ub uc un quantified db dc dn f HC)).
    right. exact (context_union_left M eb ec en nb nc nn ub uc un HU f HF). }
  assert (HN':source_full_prv M db dc dn neg).
  { apply (source_full_prv_weaken_bounded M nb nc nn db dc dn neg bound HN);[|exact HBound].
    intros f HF. apply (proj2 (context_member_cons M ub uc un quantified db dc dn f HC)).
    right. exact (context_union_right M eb ec en nb nc nn ub uc un HU f HF). }
  pose proof (source_wf_quantifier_instance M db dc dn SFAll matrix quantified witness instance
    (or_introl eq_refl) HQ HWQ' HInst) as HWI.
  pose proof (full_source_AllE M db dc dn matrix quantified witness instance HWI HPQ HQ HInst) as HPI.
  pose proof (source_wf_binary_right M db dc dn SFImpl eq bad instance
    ltac:(unfold sf_binary;auto) HI HWI) as HWBad.
  pose proof (full_source_IE M db dc dn eq bad instance HWBad HPI HE' HI) as HPBad.
  assert (HWFalse:source_sequent_wf M db dc dn (zeroM M)).
  { exists bound. split;[apply source_bounded_accept_falsity|exact HBound]. }
  pose proof (full_source_IE M db dc dn bad (zeroM M) neg HWFalse HN' HPBad HNeg) as HPFalse.
  exists ub,uc,un. split;[exact HUC|].
  apply (full_source_II M ub uc un quantified goal out db dc dn).
  - exact (source_wf_transport_context M _ _ _ out ub uc un HWO (ex_intro _ (zeroM M) HUB)).
  - apply full_source_Exp;[|exact HPFalse].
    apply (source_wf_binary_right M db dc dn SFImpl quantified goal out
      ltac:(unfold sf_binary;auto) HO).
    exact (source_wf_transport_context M _ _ _ out db dc dn HWO (ex_intro _ bound HBound)).
  - exact HC.
  - exact HO.
Qed.

Print Assumptions source_zfc_universal_refutation.
