(** Numerical witness introduction and elimination. These rules manipulate
    coded derivations; an existential theorem is never treated as a semantic
    witness in the ambient PA model. *)
From PAModel Require Import Model CodeExpressions CodeDescent FreshNames NumericalProofs NamedExistential
  NamedSelfExistential NamedSelfSpecialization NamedBinderFresh NumericalVacuitySteps NumericalEnvironments
  ContextualProofs ContextualDeduction ContextualQuantifiers ContextualPropositional
  ContextualGuardedQuantifiers QuotationPayloads SetFormulaCodes.
From PAModel Require Import ProofTemplates TemplatePropositional QuantifierMacros.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Theorem contextual_self_exists_intro M b c n x body result :
  named_binder_absent M body x -> named_exists_graph M x body result ->
  contextually_provable M b c n body -> contextually_provable M b c n result.
Proof.
  intros HA HG HP.
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
    (body .: result .: fun _=>zeroM M)) as [imp HI].
  assert (HImp : implication_graph M body result imp).
  { exact HI. }
  apply (contextual_mp M b c n body result imp HP).
  - apply contextual_global. exact (numerical_named_self_exists_intro M body x result imp HA HG HImp).
  - exact HImp.
Qed.

Theorem contextual_witness_bind M b c n x body exbody target d e m :
  context_fresh M b c n x -> formula_fresh M target x ->
  named_exists_graph M x body exbody -> environment_cons M b c n body d e m ->
  contextually_provable M b c n exbody -> contextually_provable M d e m target ->
  contextually_provable M b c n target.
Proof.
  intros HC HT HE HCons PEx PTarget.
  destruct (contextual_deduction M b c n body d e m target HCons PTarget) as [imp [HI PI]].
  exact (contextual_exists_elimination M b c n x body target exbody imp HC HT HE HI PEx PI).
Qed.

Theorem contextual_guarded_self_exists_intro M b c n x t dom body conjunction result :
  membership_graph M t x dom -> quotation_binary M SFAnd dom body conjunction ->
  named_binder_absent M conjunction x -> quotation_quantifier M false x t body result ->
  contextually_provable M b c n dom -> contextually_provable M b c n body ->
  contextually_provable M b c n result.
Proof.
  intros HD HC HA HG PD PB.
  apply (contextual_self_exists_intro M b c n x conjunction result HA).
  - exact (proj1 (quotation_guarded_exists_graph M x t body dom conjunction result HD HC) HG).
  - exact (contextual_conjunction_intro M b c n dom body conjunction PD PB HC).
Qed.

Theorem contextual_guarded_witness_bind M b c n x t dom body conjunction exbody target d e m :
  membership_graph M t x dom -> quotation_binary M SFAnd dom body conjunction ->
  quotation_quantifier M false x t body exbody -> context_fresh M b c n x ->
  formula_fresh M target x -> environment_cons M b c n conjunction d e m ->
  contextually_provable M b c n exbody -> contextually_provable M d e m target ->
  contextually_provable M b c n target.
Proof.
  intros HD HC HE HF HT HCons PE PT.
  apply (contextual_witness_bind M b c n x conjunction exbody target d e m HF HT).
  - exact (proj1 (quotation_guarded_exists_graph M x t body dom conjunction exbody HD HC) HE).
  - exact HCons.
  - exact PE.
  - exact PT.
Qed.

Print Assumptions contextual_self_exists_intro.
Print Assumptions contextual_witness_bind.
Print Assumptions contextual_guarded_self_exists_intro.
Print Assumptions contextual_guarded_witness_bind.

Lemma template_exists_map guards x p q : template_proof guards
  (E_wim (E_wal x (E_wim p q)) (E_wim (E_wex x p) (E_wex x q))).
Proof.
  unfold E_wex.
  apply (template_discharge guards). apply template_deduction.
  eapply dmp with (a:=E_wim (E_wal x (E_wn q)) (E_wal x (E_wn p))).
  - apply dthm,template_contraposition.
  - eapply dmp with (a:=E_wal x (E_wim (E_wn q) (E_wn p))).
    + apply dthm,template_r2.
    + eapply dmp with (a:=E_wal x (E_wim p q)).
      * apply dthm. eapply TP_mp.
        -- apply TP_gen,template_contraposition.
        -- apply template_r2.
      * apply dhyp;cbn;auto.
Qed.

Theorem contextual_witness_map M b c n x body target exbody extarget d e m :
  context_fresh M b c n x -> named_exists_graph M x body exbody ->
  named_exists_graph M x target extarget -> environment_cons M b c n body d e m ->
  contextually_provable M b c n exbody -> contextually_provable M d e m target ->
  contextually_provable M b c n extarget.
Proof.
  intros HF HEbody HEtarget HCons PEx PTarget.
  destruct (contextual_deduction M b c n body d e m target HCons PTarget) as [imp [HImp PImp]].
  set (rho:=x .: body .: target .: fun _=>zeroM M).
  assert (GI : code_relation M rho (E_wim (CEvar 1) (CEvar 2)) imp) by exact HImp.
  assert (GEbody : code_relation M rho (E_wex (CEvar 0) (CEvar 1)) exbody).
  { exact (proj2 (named_exists_expression M rho (CEvar 0) (CEvar 1) x body exbody eq_refl eq_refl) HEbody). }
  assert (GEtarget : code_relation M rho (E_wex (CEvar 0) (CEvar 2)) extarget).
  { exact (proj2 (named_exists_expression M rho (CEvar 0) (CEvar 2) x target extarget eq_refl eq_refl) HEtarget). }
  destruct (code_relation_total M (E_wal (CEvar 0) (E_wim (CEvar 1) (CEvar 2))) rho) as [allimp GA].
  assert (PA : contextually_provable M b c n allimp).
  { apply (contextual_gen M b c n x imp allimp HF PImp).
    exact (expression_universal_graph M rho (CEvar 0) (E_wim (CEvar 1) (CEvar 2)) x imp allimp eq_refl GI GA). }
  destruct (code_relation_total M (E_wim (E_wex (CEvar 0) (CEvar 1))
    (E_wex (CEvar 0) (CEvar 2))) rho) as [out GO].
  destruct (code_relation_total M (E_wim (E_wal (CEvar 0) (E_wim (CEvar 1) (CEvar 2)))
    (E_wim (E_wex (CEvar 0) (CEvar 1)) (E_wex (CEvar 0) (CEvar 2)))) rho) as [rule GR].
  assert (PR : numerically_provable M rule).
  { exact (unguarded_template_sound M rho _ (template_exists_map nil (CEvar 0) (CEvar 1) (CEvar 2)) rule GR). }
  assert (PO : contextually_provable M b c n out).
  { apply (contextual_mp M b c n allimp out rule PA (contextual_global M b c n rule PR)).
    exact (expression_implication_graph M rho _ _ allimp out rule GA GO GR). }
  apply (contextual_mp M b c n exbody extarget out PEx PO).
  exact (expression_implication_graph M rho _ _ exbody extarget out GEbody GEtarget GO).
Qed.

Print Assumptions template_exists_map.
Print Assumptions contextual_witness_map.

Theorem contextual_self_all_specialize M b c n x body allbody :
  named_binder_absent M body x -> universal_graph M x body allbody ->
  contextually_provable M b c n allbody -> contextually_provable M b c n body.
Proof.
  intros HA HG HP.
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
    (allbody .: body .: fun _=>zeroM M)) as [imp HI].
  assert (HImp : implication_graph M allbody body imp) by exact HI.
  apply (contextual_mp M b c n allbody body imp HP).
  - apply contextual_global. exact (numerical_named_self_specialization M body x allbody imp HA HG HImp).
  - exact HImp.
Qed.

Theorem contextual_guarded_self_all_specialize M b c n x t body dom guard allbody :
  membership_graph M t x dom -> implication_graph M dom body guard ->
  named_binder_absent M guard x -> quotation_quantifier M true x t body allbody ->
  contextually_provable M b c n allbody -> contextually_provable M b c n dom ->
  contextually_provable M b c n body.
Proof.
  intros HD HI HA HG HP PD.
  apply (contextual_mp M b c n dom body guard PD).
  - apply (contextual_self_all_specialize M b c n x guard allbody HA).
    + exact (proj1 (quotation_guarded_all_graph M x t body dom guard allbody HD HI) HG).
    + exact HP.
  - exact HI.
Qed.

Print Assumptions contextual_self_all_specialize.
Print Assumptions contextual_guarded_self_all_specialize.
