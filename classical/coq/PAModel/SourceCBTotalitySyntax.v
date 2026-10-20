(** Renaming the canonical prior CB goal exchanges its container and
    newest parameter. Its ordinal body is exactly the literal Qf matrix. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
  NumericalRenamingMaps NumericalRenaming SourceRenamingIdentity SourceCBGoal SourceQfRecipe SourceQfFunctionality
  SourceDn SourceSwap SourceFixedSwap SourceOrdinalPredicate.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Theorem source_qf_exchange_lifted_swap M rb rc rn:
  renaming_lift M(code_numeral M 3)(code_numeral M 1)(code_numeral M 2)(zeroM M)rb rc rn ->
  renaming_equivalent M(code_numeral M 210)(code_numeral M 6)(code_numeral M 3)rb rc rn(zeroM M).
Proof.
  intro HL.
  assert(Common:forall i,exists w,
    renaming_lookup M(code_numeral M 210)(code_numeral M 6)(code_numeral M 3)(zeroM M)i w /\
    renaming_lookup M rb rc rn(zeroM M)i w).
  { intro i.
    destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)
      as[E|[idx E]];subst i.
    - exists(zeroM M). split;[apply source_qf_exchange_zero|exact(proj1(proj2 HL))].
    - destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)idx)
        as[E|[idx' E]];subst idx.
      + exists(code_numeral M 2). split;[apply source_qf_exchange_one|].
        exact(proj2(proj2 HL)(zeroM M)(code_numeral M 1)(proj1(source_fixed_swap_map M))).
      + destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)idx')
          as[E|[tail E]];subst idx'.
        * exists(code_numeral M 1). split;[apply source_qf_exchange_two|].
          exact(proj2(proj2 HL)(code_numeral M 1)(zeroM M)(proj2(source_fixed_swap_map M))).
        * exists(succM M(succM M(succM M tail))). split.
          -- apply source_qf_exchange_outside. intro H. apply(coding_not_lt_zero M tail).
             exact(proj1(coding_lt_succ_cancel M tail(zeroM M))
               (proj1(coding_lt_succ_cancel M(succM M tail)(code_numeral M 1))
                 (proj1(coding_lt_succ_cancel M(succM M(succM M tail))(code_numeral M 2))H))).
          -- exact(proj2(proj2 HL)(succM M(succM M tail))(succM M(succM M tail))
               (source_swap_tail M(code_numeral M 3)(code_numeral M 1)tail)). }
  intros i v. destruct(Common i) as(w&HA&HB). split;intro H.
  - pose proof(renaming_lookup_functional M _ _ _ _ i v w H HA) as E. now subst v.
  - pose proof(renaming_lookup_functional M _ _ _ _ i v w H HB) as E. now subst v.
Qed.

Theorem source_cb_swap_body_qf M domain level count phi goal q swapped:
  source_cb_goal M domain level(source_ordinal_predicate_code M)count phi goal ->
  source_qf_recipe M domain level count phi q ->
  numerical_renaming M goal(code_numeral M 3)(code_numeral M 1)(code_numeral M 2)(zeroM M)swapped ->
  exists body,sf_relation M SFAnd(source_ordinal_predicate_code M)q body /\
    sf_relation M SFEx body(zeroM M)swapped.
Proof.
  intros(d0&dn&body&HD0&HDN&HBody&HEx)(d0'&dn'&HD0'&HDN'&HQ)HR.
  pose proof(source_d0_recipe_functional M domain level phi d0' d0 HD0' HD0) as E. subst d0'.
  pose proof(source_dn_functional M count d0 dn' dn HDN' HDN) as E. subst dn'.
  destruct(proj1(numerical_renaming_quantifier M false body goal(code_numeral M 3)(code_numeral M 1)
    (code_numeral M 2)(zeroM M)swapped HEx)HR) as(rb&rc&rn&body'&HL&HBodyR&HOut).
  destruct(proj1(numerical_renaming_binary M SFAnd(source_ordinal_predicate_code M)dn body rb rc rn(zeroM M)
    body'(or_introl eq_refl)HBody)HBodyR) as(ordinal'&dn''&HOrd&HDN''&HBody').
  pose proof(numerical_renaming_lift_fixes_domain M(source_ordinal_predicate_code M)
    (code_numeral M 3)(code_numeral M 1)(code_numeral M 2)(zeroM M)rb rc rn
    (source_ordinal_predicate_bounded M)HL) as HOrdSelf.
  pose proof(numerical_renaming_functional M(source_ordinal_predicate_code M)rb rc rn(zeroM M)
    ordinal'(source_ordinal_predicate_code M)HOrd HOrdSelf) as E. subst ordinal'.
  pose proof(proj1(numerical_renaming_extensional M dn(code_numeral M 210)(code_numeral M 6)
    (code_numeral M 3)rb rc rn(zeroM M)q(source_qf_exchange_lifted_swap M rb rc rn HL))HQ) as HQ'.
  pose proof(numerical_renaming_functional M dn rb rc rn(zeroM M)dn'' q HDN'' HQ') as E. subst dn''.
  exists body'. auto.
Qed.

Print Assumptions source_qf_exchange_lifted_swap.
Print Assumptions source_cb_swap_body_qf.
