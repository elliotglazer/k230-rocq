(** Literal guarded quotation rules.  Substitution and binder hygiene remain
    explicit premises; these rules do not assume a quotation preservation
    theorem or invariance of the raw falsity code under named substitution. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing CodeExpressions CodeDescent CodeTags
  NumericalProofs ProofTemplates NumericalEnvironments NumericalContexts FreshNames
  ContextualProofs ContextualDeduction ContextualPropositional
  NumericalVacuitySteps NumericalVacuity NamedLeibnizSteps
  NamedSubstitution NamedSubstitutionFunctionality NamedSubstitutionLaws NamedBinderFresh NamedExistential
  ContextualQuantifiers SetFormulaCodes QuotationPayloads.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Lemma guarded_implication_nonzero M t x dom body guard :
  membership_graph M t x dom -> implication_graph M dom body guard -> guard<>zeroM M.
Proof.
  intros Hdom Hguard Eguard. subst guard.
  apply implication_graph_tagged in Hguard.
  assert (Hzero : tagged_pair_graph M 0 (zeroM M) (zeroM M) (zeroM M)).
  { exists (zeroM M). split;[apply pair_zero|].
    change (zeroM M = addM M (mulM M (code_numeral M 4) (zeroM M)) (zeroM M)).
    rewrite (Arithmetic.mul_comm M (code_numeral M 4) (zeroM M)),
      Arithmetic.mul_zero,Arithmetic.add_zero. reflexivity. }
  destruct (tagged_pair_decode_unique M 0 0 dom body (zeroM M) (zeroM M) (zeroM M)
    ltac:(lia) ltac:(lia) Hguard Hzero) as [_ [Edom _]].
  exact (named_tag_nonzero M 1 t x dom ltac:(lia) Hdom Edom).
Qed.

Lemma quotation_guarded_all_graph M x t body dom guard result :
  membership_graph M t x dom -> implication_graph M dom body guard ->
  (quotation_quantifier M true x t body result <-> universal_graph M x guard result).
Proof.
  intros Hdom Hguard.
  set (env:=x .: t .: body .: fun _ => zeroM M).
  assert (Ed : code_relation M env (E_wel (CEvar 1) (CEvar 0)) dom).
  { exact (proj2 (ns_atom_expression M env false (CEvar 1) (CEvar 0) t x dom eq_refl eq_refl) Hdom). }
  assert (Eg : code_relation M env (E_wim (E_wel (CEvar 1) (CEvar 0)) (CEvar 2)) guard).
  { exact (proj2 (expression_implication_iff M env (E_wel (CEvar 1) (CEvar 0)) (CEvar 2)
      dom body guard Ed eq_refl) Hguard). }
  exact (expression_universal_iff M env (CEvar 0)
    (E_wim (E_wel (CEvar 1) (CEvar 0)) (CEvar 2)) x guard result eq_refl Eg).
Qed.

Lemma quotation_guarded_exists_graph M x t body dom conjunction result :
  membership_graph M t x dom -> quotation_binary M SFAnd dom body conjunction ->
  (quotation_quantifier M false x t body result <-> named_exists_graph M x conjunction result).
Proof.
  intros Hdom Hconj.
  set (env:=x .: t .: body .: fun _ => zeroM M).
  assert (Ed : code_relation M env (E_wel (CEvar 1) (CEvar 0)) dom).
  { exact (proj2 (ns_atom_expression M env false (CEvar 1) (CEvar 0) t x dom eq_refl eq_refl) Hdom). }
  assert (Ec : code_relation M env (E_wa (E_wel (CEvar 1) (CEvar 0)) (CEvar 2)) conjunction).
  { change (code_relation M env
      (code_subst (arguments2 (E_wel (CEvar 1) (CEvar 0)) (CEvar 2) (CEconst 0))
        (E_wa (CEvar 0) (CEvar 1))) conjunction).
    apply (proj2 (code_subst_graph M env
      (arguments2 (E_wel (CEvar 1) (CEvar 0)) (CEvar 2) (CEconst 0))
      (arguments2 dom body (zeroM M))
      ltac:(intros [|[|i]];[exact Ed|reflexivity|reflexivity])
      (E_wa (CEvar 0) (CEvar 1)) conjunction)).
    exact Hconj. }
  exact (named_exists_expression M env (CEvar 0)
    (E_wa (E_wel (CEvar 1) (CEvar 0)) (CEvar 2)) x conjunction result eq_refl Ec).
Qed.

Theorem contextual_guarded_all_intro M b c n x t body dom d e m result :
  membership_graph M t x dom -> environment_cons M b c n dom d e m ->
  context_fresh M b c n x -> contextually_provable M d e m body ->
  quotation_quantifier M true x t body result -> contextually_provable M b c n result.
Proof.
  intros Hdom Hcons Hfresh Hbody Hresult.
  destruct (contextual_deduction M b c n dom d e m body Hcons Hbody)
    as [guard [Hguard Pguard]].
  apply (contextual_gen M b c n x guard result Hfresh Pguard).
  exact (proj1 (quotation_guarded_all_graph M x t body dom guard result Hdom Hguard) Hresult).
Qed.

Theorem contextual_guarded_all_specialize M b c n x y t body body' dom dom' guard guard' all :
  x<>y -> membership_graph M t x dom -> membership_graph M t y dom' ->
  implication_graph M dom body guard -> implication_graph M dom' body' guard' ->
  named_binder_absent M guard x -> named_binder_absent M guard y ->
  named_substitution M guard x y guard' -> quotation_quantifier M true x t body all ->
  contextually_provable M b c n all -> contextually_provable M b c n dom' ->
  contextually_provable M b c n body'.
Proof.
  intros Hxy Hdom Hdom' Hguard Hguard' Hx Hy Hsub Hall Pall Pdom'.
  assert (Pguard' : contextually_provable M b c n guard').
  { apply (contextual_named_specialization M b c n guard x y guard' all Hxy Hx Hy Hsub).
    - exact (proj1 (quotation_guarded_all_graph M x t body dom guard all Hdom Hguard) Hall).
    - exact Pall. }
  exact (contextual_mp M b c n dom' body' guard' Pdom' Pguard' Hguard').
Qed.

Corollary contextual_guarded_all_specialize_parts M b c n x y t body body' dom dom' guard guard' all :
  x<>y -> membership_graph M t x dom -> membership_graph M t y dom' ->
  implication_graph M dom body guard -> implication_graph M dom' body' guard' ->
  named_binder_absent M guard x -> named_binder_absent M guard y ->
  named_substitution M dom x y dom' -> named_substitution M body x y body' ->
  quotation_quantifier M true x t body all ->
  contextually_provable M b c n all -> contextually_provable M b c n dom' ->
  contextually_provable M b c n body'.
Proof.
  intros Hxy Hdom Hdom' Hguard Hguard' Hx Hy Hdsub Hbsub Hall Pall Pdom'.
  apply (contextual_guarded_all_specialize M b c n x y t body body' dom dom' guard guard' all
    Hxy Hdom Hdom' Hguard Hguard' Hx Hy);[|exact Hall|exact Pall|exact Pdom'].
  apply (proj2 (named_substitution_implication_iff M dom body guard x y guard' Hxy
    (guarded_implication_nonzero M t x dom body guard Hdom Hguard) Hguard)).
  exists dom',body'. auto.
Qed.

Theorem contextual_guarded_exists_intro M b c n x y t body body' dom dom' conjunction conjunction' result :
  x<>y -> membership_graph M t x dom -> membership_graph M t y dom' ->
  quotation_binary M SFAnd dom body conjunction ->
  quotation_binary M SFAnd dom' body' conjunction' ->
  named_binder_absent M conjunction x -> named_binder_absent M conjunction y ->
  named_substitution M conjunction x y conjunction' ->
  quotation_quantifier M false x t body result ->
  contextually_provable M b c n dom' -> contextually_provable M b c n body' ->
  contextually_provable M b c n result.
Proof.
  intros Hxy Hdom Hdom' Hconj Hconj' Hx Hy Hsub Hresult Pdom' Pbody'.
  apply (contextual_named_exists_intro M b c n conjunction x y conjunction' result Hxy Hx Hy Hsub).
  - exact (proj1 (quotation_guarded_exists_graph M x t body dom conjunction result Hdom Hconj) Hresult).
  - exact (contextual_conjunction_intro M b c n dom' body' conjunction' Pdom' Pbody' Hconj').
Qed.
