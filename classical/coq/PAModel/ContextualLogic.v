(** Concrete K logical operations inside an internally coded context. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  ProofTemplates TemplateCD TemplatePropositional NumericalVacuitySteps
  NumericalVacuity ContextualProofs FreshNames.
Unset Implicit Arguments.

Lemma contextual_template M b c n env e v : template_proof nil e ->
  code_relation M env e v -> contextually_provable M b c n v.
Proof.
  intros He Hv. apply contextual_global.
  exact (unguarded_template_sound M env e He v Hv).
Qed.

Lemma contextual_mp_expression M b c n env p q a z h :
  code_relation M env p a -> code_relation M env q z ->
  code_relation M env (E_wim p q) h ->
  contextually_provable M b c n a -> contextually_provable M b c n h ->
  contextually_provable M b c n z.
Proof.
  intros Hp Hq Hh Ha Himp. apply (contextual_mp M b c n a z h Ha Himp).
  exact (expression_implication_graph M env p q a z h Hp Hq Hh).
Qed.

Theorem contextual_implication_intro M b c n h f :
  contextually_provable M b c n f ->
  exists g, implication_graph M h f g /\ contextually_provable M b c n g.
Proof.
  intro Hf. set (env := code_parameters h f (zeroM M) (zeroM M)).
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1)) env) as [g Hg].
  destruct (code_relation_total M (E_wim (CEvar 1) (E_wim (CEvar 0) (CEvar 1))) env) as [k Hk].
  exists g. split.
  - exact (expression_implication_graph M env (CEvar 0) (CEvar 1) h f g eq_refl eq_refl Hg).
  - apply (contextual_mp_expression M b c n env (CEvar 1)
      (E_wim (CEvar 0) (CEvar 1)) f g k eq_refl Hg Hk Hf).
    eapply contextual_template; [apply template_K|exact Hk].
Qed.

Theorem contextual_identity M b c n h :
  exists g, implication_graph M h h g /\ contextually_provable M b c n g.
Proof.
  set (env := fun _ : nat => h).
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 0)) env) as [g Hg].
  exists g. split.
  - exact (expression_implication_graph M env (CEvar 0) (CEvar 0) h h g eq_refl eq_refl Hg).
  - eapply contextual_template; [apply template_I|exact Hg].
Qed.

Theorem contextual_deduction_mp M b c n h a z az ha haz :
  implication_graph M a z az -> implication_graph M h a ha ->
  implication_graph M h az haz -> contextually_provable M b c n ha ->
  contextually_provable M b c n haz ->
  exists hz, implication_graph M h z hz /\ contextually_provable M b c n hz.
Proof.
  intros Haz Hha Hhaz Hpha Hphaz.
  set (env := code_parameters h a z (zeroM M)).
  pose proof (proj2 (expression_implication_iff M env (CEvar 1) (CEvar 2)
    a z az eq_refl eq_refl) Haz) as Eaz.
  pose proof (proj2 (expression_implication_iff M env (CEvar 0) (CEvar 1)
    h a ha eq_refl eq_refl) Hha) as Eha.
  pose proof (proj2 (expression_implication_iff M env (CEvar 0) _
    h az haz eq_refl Eaz) Hhaz) as Ehaz.
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 2)) env) as [hz Ehz].
  destruct (code_relation_total M (E_wim (E_wim (CEvar 0) (CEvar 1))
    (E_wim (CEvar 0) (CEvar 2))) env) as [mid Emid].
  destruct (code_relation_total M
    (E_wim (E_wim (CEvar 0) (E_wim (CEvar 1) (CEvar 2)))
      (E_wim (E_wim (CEvar 0) (CEvar 1)) (E_wim (CEvar 0) (CEvar 2)))) env) as [s Es].
  assert (Hmid : contextually_provable M b c n mid).
  { eapply contextual_mp_expression; [exact Ehaz|exact Emid|exact Es|exact Hphaz|].
    eapply contextual_template; [apply template_S|exact Es]. }
  exists hz. split.
  - exact (expression_implication_graph M env (CEvar 0) (CEvar 2) h z hz eq_refl eq_refl Ehz).
  - exact (contextual_mp_expression M b c n env _ _ ha hz mid Eha Ehz Emid Hpha Hmid).
Qed.

Theorem contextual_generalization_under_hypothesis M b c n x h f premise quantified :
  context_fresh M b c n x -> formula_fresh M h x ->
  implication_graph M h f premise -> universal_graph M x f quantified ->
  contextually_provable M b c n premise ->
  exists result, implication_graph M h quantified result /\ contextually_provable M b c n result.
Proof.
  intros Hctx Hfresh Hprem Hquant Hproof.
  set (env := code_parameters x h f (zeroM M)).
  pose proof (proj2 (expression_implication_iff M env (CEvar 1) (CEvar 2)
    h f premise eq_refl eq_refl) Hprem) as Eprem.
  pose proof (proj2 (expression_universal_iff M env (CEvar 0) (CEvar 2)
    x f quantified eq_refl eq_refl) Hquant) as Equant.
  destruct (code_relation_total M (E_wal (CEvar 0) (CEvar 1)) env) as [allh Eallh].
  destruct (code_relation_total M (E_wal (CEvar 0) (E_wim (CEvar 1) (CEvar 2))) env)
    as [allprem Eallprem].
  assert (Hallprem : contextually_provable M b c n allprem).
  { apply (contextual_gen M b c n x premise allprem Hctx Hproof).
    exact (expression_universal_graph M env (CEvar 0) (E_wim (CEvar 1) (CEvar 2)) x premise allprem eq_refl Eprem Eallprem). }
  destruct (code_relation_total M (E_wim (E_wal (CEvar 0) (CEvar 1))
    (E_wal (CEvar 0) (CEvar 2))) env) as [mid Emid].
  destruct (code_relation_total M
    (E_wim (E_wal (CEvar 0) (E_wim (CEvar 1) (CEvar 2)))
      (E_wim (E_wal (CEvar 0) (CEvar 1)) (E_wal (CEvar 0) (CEvar 2)))) env) as [r Er].
  assert (Hmid : contextually_provable M b c n mid).
  { eapply contextual_mp_expression; [exact Eallprem|exact Emid|exact Er|exact Hallprem|].
    eapply contextual_template; [apply template_r2|exact Er]. }
  destruct (code_relation_total M (E_vac (CEvar 0) (CEvar 1)) env) as [vac Evac].
  assert (Hvac : contextually_provable M b c n vac).
  { apply contextual_global. apply (numerical_vacuity M x h vac Hfresh).
    exact (proj1 (expression_vacuity_graph M env (CEvar 0) (CEvar 1)
      x h vac eq_refl eq_refl) Evac). }
  destruct (code_relation_total M (E_wim (CEvar 1) (E_wal (CEvar 0) (CEvar 2))) env)
    as [result Eresult].
  destruct (code_relation_total M
    (E_wim (E_wim (CEvar 1) (E_wal (CEvar 0) (CEvar 1)))
      (E_wim (E_wim (E_wal (CEvar 0) (CEvar 1)) (E_wal (CEvar 0) (CEvar 2)))
        (E_wim (CEvar 1) (E_wal (CEvar 0) (CEvar 2))))) env) as [s Es].
  destruct (code_relation_total M
    (E_wim (E_wim (E_wal (CEvar 0) (CEvar 1)) (E_wal (CEvar 0) (CEvar 2)))
      (E_wim (CEvar 1) (E_wal (CEvar 0) (CEvar 2)))) env) as [bridge Ebridge].
  assert (Hbridge : contextually_provable M b c n bridge).
  { eapply contextual_mp_expression; [exact Evac|exact Ebridge|exact Es|exact Hvac|].
    eapply contextual_template; [apply template_B|exact Es]. }
  exists result. split.
  - exact (expression_implication_graph M env (CEvar 1) (E_wal (CEvar 0) (CEvar 2)) h quantified result eq_refl Equant Eresult).
  - eapply contextual_mp_expression; [exact Emid|exact Eresult|exact Ebridge|exact Hmid|exact Hbridge].
Qed.

Print Assumptions contextual_implication_intro.
Print Assumptions contextual_identity.
Print Assumptions contextual_deduction_mp.
Print Assumptions contextual_generalization_under_hypothesis.


