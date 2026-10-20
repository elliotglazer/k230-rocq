(** The CB induction hypothesis supplies the actual universally guarded
    totality proof needed by ordinal collection. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
  NumericalRenamingMaps NumericalRenaming NumericalInstantiation SourceFixedSwap SourceSwap
  SourceDomainInstances SourceDomainInstanceRenaming SourceDescriptorClosure SourceDescriptorProvability
  SourceSetTheoryDescriptors SourceZFRProvability SourceLFixed SourceHierarchySyntax SourceOrdinalPredicate
  SourceCBGoal SourceQfRecipe SourceCBProofProperty SourceCBTotalitySyntax SourceCBAllIntroduction.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code source_L_domain_code.

Definition source_cb_totality_graph M q out :=exists body witness guard point,
  sf_relation M SFAnd(source_ordinal_predicate_code M)q body /\
  sf_relation M SFEx body(zeroM M)witness /\
  sf_relation M SFMember(zeroM M)(code_numeral M 1)guard /\
  sf_relation M SFImpl guard witness point /\sf_relation M SFAll point(zeroM M)out.

Theorem source_cb_totality_total M q:exists out,source_cb_totality_graph M q out.
Proof.
  destruct(sf_relation_total M SFAnd(source_ordinal_predicate_code M)q) as(body&HB).
  destruct(sf_relation_total M SFEx body(zeroM M)) as(witness&HW).
  destruct(sf_relation_total M SFMember(zeroM M)(code_numeral M 1)) as(guard&HG).
  destruct(sf_relation_total M SFImpl guard witness) as(point&HP).
  destruct(sf_relation_total M SFAll point(zeroM M)) as(out&HO).
  exists out,body,witness,guard,point. auto.
Qed.

Lemma source_cb_inserted_ordinal_name M g n:
  coding_lt M g(succM M n) ->exists inserted,
    coding_lt M inserted(succM M(succM M n)) /\
    renaming_lookup M(code_numeral M 3)(code_numeral M 1)(code_numeral M 2)(zeroM M)
      inserted(succM M g).
Proof.
  intro HG. destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H)g) as[E|[i E]];subst g.
  - exists(zeroM M). split;[apply coding_zero_lt_succ|exact(proj1(source_fixed_swap_map M))].
  - exists(succM M(succM M i)). split.
    + exact(proj2(coding_lt_succ_cancel M(succM M i)(succM M n))HG).
    + apply source_swap_tail.
Qed.

Theorem source_cb_ih_totality M level count phi q g ordinal total result n:
  source_LL_instance M(code_numeral M 1)(zeroM M)level ->
  source_cb_proof_at M(source_L_domain_code M)level(source_ordinal_predicate_code M)count ->
  source_bounded M phi(addM M count(succM M(succM M n))) ->coding_lt M g(succM M n) ->
  source_qf_recipe M(source_L_domain_code M)level count phi q ->
  numerical_instantiation M(source_ordinal_predicate_code M)g ordinal ->
  source_cb_totality_graph M q total ->sf_relation M SFImpl ordinal total result ->
  source_zfr_provable M result.
Proof.
  intros HL IH HB HG HQ HOrd(body&witness&guard&point&HBody&HEx&HGuard&HPoint&HAll)HResult.
  destruct(source_cb_goal_total M(source_L_domain_code M)level(source_ordinal_predicate_code M)count phi)
    as(goal&HGoal).
  destruct(source_cb_inserted_ordinal_name M g n HG) as(inserted&HI&HLookup).
  destruct(numerical_instantiation_total M(source_ordinal_predicate_code M)inserted) as(oi&HOI).
  destruct(sf_relation_total M SFImpl oi goal) as(imp&HImp).
  pose proof(IH phi(succM M n)inserted oi goal imp HB HI HOI HGoal HImp) as PImp.
  destruct(numerical_renaming_total M goal(code_numeral M 3)(code_numeral M 1)
    (code_numeral M 2)(zeroM M)) as(swapped&HS).
  destruct(source_cb_swap_body_qf M(source_L_domain_code M)level count phi goal q swapped HGoal HQ HS)
    as(body'&HBody'&HEx').
  pose proof(sf_relation_functional M SFAnd(source_ordinal_predicate_code M)q body' body HBody' HBody) as E.
  subst body'.
  pose proof(sf_relation_functional M SFEx body(zeroM M)swapped witness HEx' HEx) as E. subst swapped.
  destruct(numerical_renaming_total M ordinal(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))
    as(shifted&HShift).
  pose proof(source_domain_instance_shift M(source_ordinal_predicate_code M)g ordinal shifted
    (source_ordinal_predicate_bounded M)HOrd HShift) as HShiftOrd.
  destruct(numerical_renaming_total M oi(code_numeral M 3)(code_numeral M 1)
    (code_numeral M 2)(zeroM M)) as(renamed&HR).
  pose proof(source_domain_instance_renaming M(source_ordinal_predicate_code M)inserted oi
    (code_numeral M 3)(code_numeral M 1)(code_numeral M 2)(zeroM M)renamed(succM M g)
    (source_ordinal_predicate_bounded M)HOI HR HLookup) as HR' .
  pose proof(numerical_instantiation_functional M(source_ordinal_predicate_code M)(succM M g)
    renamed shifted HR' HShiftOrd) as E. subst renamed.
  destruct(sf_relation_total M SFImpl shifted witness) as(pointImp&HPI).
  assert(HRImp:numerical_renaming M imp(code_numeral M 3)(code_numeral M 1)
      (code_numeral M 2)(zeroM M)pointImp).
  { apply(proj2(numerical_renaming_binary M SFImpl oi goal imp(code_numeral M 3)(code_numeral M 1)
      (code_numeral M 2)(zeroM M)pointImp(or_intror(or_intror eq_refl))HImp)).
    exists shifted,witness. auto. }
  pose proof(source_descriptor_provable_renaming M ZFRSourceDescriptor imp(code_numeral M 3)
    (code_numeral M 1)(code_numeral M 2)(zeroM M)pointImp PImp HRImp) as PPointImp.
  apply(source_zfr_cb_all_intro M ordinal shifted guard witness point total pointImp result(succM M n)).
  - exact(source_domain_instance_bound M(source_ordinal_predicate_code M)g ordinal(succM M n)
      (source_ordinal_predicate_bounded M)HG HOrd).
  - apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(code_numeral M 1)guard
      (succM M(succM M n))(or_introl eq_refl)HGuard)).
    split;[apply coding_zero_lt_succ|exact(proj2(coding_lt_succ_cancel M(zeroM M)(succM M n))
      (coding_zero_lt_succ M n))].
  - apply(source_fixed_swap_bounded M goal witness n);[|exact HS].
    exact(source_cb_goal_bounded M(source_L_domain_code M)level(source_ordinal_predicate_code M)
      count phi goal(succM M n)(numerical_L_domain_bounded M)
      (source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
        (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HL)
      (source_ordinal_predicate_bounded M)HB HGoal).
  - exact HShift.
  - exact HPoint.
  - exact HAll.
  - exact HPI.
  - exact HResult.
  - exact(proj1(source_zfr_descriptor_provable M pointImp)PPointImp).
Qed.

Print Assumptions source_cb_totality_total.
Print Assumptions source_cb_inserted_ordinal_name.
Print Assumptions source_cb_ih_totality.
