(** Named quantifier operations in internally coded contexts.  The sole
    generalization of a contextual premise below is guarded by context_fresh.
    All other proof programs used here construct global K theorems. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  ProofTemplates NumericalVacuitySteps NumericalVacuity FreshNames
  ContextualProofs NamedSubstitution NamedBinderFresh NamedLeibnizSteps
  NamedSpecialization NamedExistential.
Unset Implicit Arguments.

Theorem contextual_named_specialization M b c n f x y v allf :
  x<>y -> named_binder_absent M f x -> named_binder_absent M f y ->
  named_substitution M f x y v -> universal_graph M x f allf ->
  contextually_provable M b c n allf -> contextually_provable M b c n v.
Proof.
  intros Hxy Hx Hy Hv Hall HP.
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
    (arguments2 allf v (zeroM M))) as [result Hresult].
  apply (contextual_mp M b c n allf v result HP).
  - apply contextual_global.
    exact (numerical_named_specialization M f x y v allf result Hxy Hx Hy Hv Hall Hresult).
  - exact Hresult.
Qed.

Theorem contextual_named_exists_intro M b c n f x y v exf :
  x<>y -> named_binder_absent M f x -> named_binder_absent M f y ->
  named_substitution M f x y v -> named_exists_graph M x f exf ->
  contextually_provable M b c n v -> contextually_provable M b c n exf.
Proof.
  intros Hxy Hx Hy Hv Hex HP.
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
    (arguments2 v exf (zeroM M))) as [result Hresult].
  apply (contextual_mp M b c n v exf result HP).
  - apply contextual_global.
    exact (numerical_named_exists_intro M f x y v exf result Hxy Hx Hy Hv Hex Hresult).
  - exact Hresult.
Qed.

Theorem contextual_exists_elimination M b c n x f g exf premise :
  context_fresh M b c n x -> formula_fresh M g x ->
  named_exists_graph M x f exf -> implication_graph M f g premise ->
  contextually_provable M b c n exf -> contextually_provable M b c n premise ->
  contextually_provable M b c n g.
Proof.
  intros Hctx Hg Hex Hprem Pex Pprem.
  set (env:=code_parameters x f g (zeroM M)).
  assert (Eprem : code_relation M env (E_wim (CEvar 1) (CEvar 2)) premise).
  { exact (proj2 (expression_implication_iff M env (CEvar 1) (CEvar 2) f g premise eq_refl eq_refl) Hprem). }
  assert (Eex : code_relation M env (E_wex (CEvar 0) (CEvar 1)) exf).
  { exact (proj2 (named_exists_expression M env (CEvar 0) (CEvar 1) x f exf eq_refl eq_refl) Hex). }
  destruct (code_relation_total M (E_wal (CEvar 0) (E_wim (CEvar 1) (CEvar 2))) env)
    as [allprem Eallprem].
  assert (Pallprem : contextually_provable M b c n allprem).
  { apply (contextual_gen M b c n x premise allprem Hctx Pprem).
    exact (expression_universal_graph M env (CEvar 0) (E_wim (CEvar 1) (CEvar 2))
      x premise allprem eq_refl Eprem Eallprem). }
  destruct (code_relation_total M (E_wim (E_wex (CEvar 0) (CEvar 1)) (CEvar 2)) env)
    as [eximp Eeximp].
  destruct (code_relation_total M
    (E_wim (E_wal (CEvar 0) (E_wim (CEvar 1) (CEvar 2)))
      (E_wim (E_wex (CEvar 0) (CEvar 1)) (CEvar 2))) env) as [rule Erule].
  assert (Prule : numerically_provable M rule).
  { apply (ns_proof_exists_elimination M env (CEvar 0) (CEvar 1) (CEvar 2));[|exact Erule].
    intros q Hq. apply (numerical_vacuity M x g q Hg).
    exact (proj1 (expression_vacuity_graph M env (CEvar 0) (CEvar 2) x g q eq_refl eq_refl) Hq). }
  assert (Peximp : contextually_provable M b c n eximp).
  { apply (contextual_mp M b c n allprem eximp rule Pallprem (contextual_global M b c n rule Prule)).
    exact (expression_implication_graph M env
      (E_wal (CEvar 0) (E_wim (CEvar 1) (CEvar 2)))
      (E_wim (E_wex (CEvar 0) (CEvar 1)) (CEvar 2)) allprem eximp rule Eallprem Eeximp Erule). }
  apply (contextual_mp M b c n exf g eximp Pex Peximp).
  exact (expression_implication_graph M env (E_wex (CEvar 0) (CEvar 1)) (CEvar 2)
    exf g eximp Eex eq_refl Eeximp).
Qed.
