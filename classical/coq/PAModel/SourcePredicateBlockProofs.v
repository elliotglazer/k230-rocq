(** Actual source proof operations for the internally finite table of
    parameter-membership assertions used by L_common. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  SourceBounded SourceQuantifierRules NumericalContexts NumericalSourceFull SetFormulaCodes
  NumericalRenaming NumericalRenamingMaps NumericalContextRenaming
  SourceContextConjunction SourceContextConjunctionProofs SourceContextConjunctionRenaming
  SourcePredicateBlocks NumericalInstantiation SourceDomainInstances.
Unset Implicit Arguments.

Lemma source_predicate_context_bound M start domain n b c k :
  (forall i,coding_lt M i n ->coding_lt M (addM M i start) k) ->source_bounded M domain (code_numeral M 1) ->
  source_predicate_context M start domain n b c ->context_bounded M b c n k.
Proof.
  intros HNames HD HCtx f [i [HI HF]].
  exact (source_domain_instance_bound M domain (addM M i start) f k HD (HNames i HI)(HCtx i f HI HF)).
Qed.
Theorem source_predicate_block_bound M start domain n result k :
  (forall i,coding_lt M i n ->coding_lt M (addM M i start) k) ->source_bounded M domain (code_numeral M 1) ->
  source_predicate_block M start domain n result ->source_bounded M result k.
Proof.
  intros HNames HD [b [c [HC HF]]].
  exact (source_context_conjunction_bound M b c n result k HF
    (source_predicate_context_bound M start domain n b c k HNames HD HC)).
Qed.
Theorem source_full_predicate_block_intro M start domain n result b c l k :
  (forall i,coding_lt M i n ->coding_lt M (addM M i start) k) ->source_bounded M domain (code_numeral M 1) ->
  source_predicate_block M start domain n result ->context_bounded M b c l k ->
  (forall i f,coding_lt M i n ->numerical_instantiation M domain (addM M i start) f ->source_full_prv M b c l f) ->
  source_full_prv M b c l result.
Proof.
  intros HNames HD [sb [sc [HSC HF]]] HC HH.
  assert (PH:forall h,context_member M sb sc n h ->source_full_prv M b c l h).
  { intros h [i [HI HHCode]]. exact (HH i h HI (HSC i h HI HHCode)). }
  exact (proj2 (source_context_conjunction_intro M n sb sc result b c l k HF
    (source_predicate_context_bound M start domain n sb sc k HNames HD HSC) HC PH)).
Qed.
Theorem source_full_predicate_block_project M start domain n result b c l k i f :
  (forall j,coding_lt M j n ->coding_lt M (addM M j start) k) ->source_bounded M domain (code_numeral M 1) ->
  source_predicate_block M start domain n result ->context_bounded M b c l k ->
  source_full_prv M b c l result ->coding_lt M i n ->numerical_instantiation M domain (addM M i start) f ->
  source_full_prv M b c l f.
Proof.
  intros HNames HD [sb [sc [HSC HF]]] HC PP HI HAtom.
  destruct (beta_total M sb sc i) as [g HG].
  pose proof (numerical_instantiation_functional M domain (addM M i start) f g HAtom (HSC i g HI HG)) as E. subst g.
  exact (source_context_conjunction_project M n sb sc result b c l k HF
    (source_predicate_context_bound M start domain n sb sc k HNames HD HSC) HC PP f (ex_intro _ i (conj HI HG))).
Qed.


Print Assumptions source_predicate_context_bound.
Print Assumptions source_predicate_block_bound.
Print Assumptions source_full_predicate_block_intro.
Print Assumptions source_full_predicate_block_project.
