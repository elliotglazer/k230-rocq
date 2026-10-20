(** Direct source proofs of All(a) iff not Ex(not a). The matrix may be
    an arbitrary PA-model code. All binder shifts and witness rules are real. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalRenaming
  NumericalSourceFull SourceQuantifierRules SourceProofRenaming SourceImplicationAllShift
  SourceContextProofHelpers SourceDerivedRules SourceExistentialMap SourceDoubleNegationElimination SourceUniversalPropositional.
Unset Implicit Arguments.

Theorem source_full_all_from_not_ex_neg M b c n a negA exNeg notEx all k:
  context_bounded M b c n k ->source_bounded M a(succM M k) ->
  sf_relation M SFImpl a(zeroM M)negA ->sf_relation M SFEx negA(zeroM M)exNeg ->
  sf_relation M SFImpl exNeg(zeroM M)notEx ->sf_relation M SFAll a(zeroM M)all ->
  source_full_prv M b c n notEx ->source_full_prv M b c n all.
Proof.
  intros BC BA HNeg HEx HNot HAll PNot.
  pose proof(proj2(source_bounded_accept_binary M SFImpl a(zeroM M)negA(succM M k)
    (or_intror(or_intror eq_refl))HNeg)(conj BA(source_bounded_accept_falsity M(succM M k))))as BNeg.
  pose proof(proj2(source_bounded_accept_unary M SFEx negA exNeg k(or_intror eq_refl)HEx)BNeg)as BEx.
  pose proof(proj2(source_bounded_accept_unary M SFAll a all k(or_introl eq_refl)HAll)BA)as BAll.
  destruct(context_shift_total M b c n)as(sb&sc&HShift).
  pose proof(context_shift_preserves_bound M b c n sb sc k HShift BC)as BS.
  destruct(numerical_renaming_total M exNeg(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))as(exS&HExS).
  destruct(sf_relation_total M SFImpl exS(zeroM M))as(notS&HNotS).
  assert(HNotShift:source_formula_shift M notEx notS).
  { apply(proj2(numerical_renaming_binary M SFImpl exNeg(zeroM M)notEx
      (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)notS(or_intror(or_intror eq_refl))HNot)).
    exists exS,(zeroM M). split;[exact HExS|]. split;[|exact HNotS].
    apply(proj2(numerical_renaming_invalid M(zeroM M)(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)(zeroM M)(or_introl eq_refl))). reflexivity. }
  pose proof(source_full_prv_renaming M b c n notEx(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)sb sc notS PNot HShift HNotShift)as PNotS.
  destruct(environment_cons_total M sb sc n negA)as(ub&uc&un&HCons).
  pose proof(proj2(context_bounded_cons M sb sc n negA ub uc un(succM M k)HCons)(conj BNeg BS))as BU.
  pose proof(source_full_cons_head M sb sc n negA ub uc un(succM M k)HCons BNeg BU)as PNeg.
  destruct(source_shifted_exists_specialization M negA exNeg exS(succM M k)BNeg HEx HExS)as(bodyS&HBodyS&HInst).
  pose proof(source_shift_bound M exNeg exS k BEx HExS)as BExS.
  pose proof(full_source_ExI M ub uc un bodyS exS(zeroM M)negA(ex_intro _ (succM M k)(conj BExS BU))PNeg HBodyS HInst)as PExS.
  pose proof(source_full_cons_weaken M sb sc n negA ub uc un(succM M k)notS HCons BU PNotS)as PNotU.
  pose proof(source_full_modus_ponens M ub uc un exS(zeroM M)notS HNotS PNotU PExS)as PFalse.
  destruct(sf_relation_total M SFImpl negA(zeroM M))as(double&HDouble).
  pose proof(proj2(source_bounded_accept_binary M SFImpl negA(zeroM M)double(succM M k)
    (or_intror(or_intror eq_refl))HDouble)(conj BNeg(source_bounded_accept_falsity M(succM M k))))as BDouble.
  pose proof(full_source_II M sb sc n negA(zeroM M)double ub uc un(ex_intro _ (succM M k)(conj BDouble BS))
    PFalse HCons HDouble)as PDouble.
  pose proof(source_full_double_negation_elimination M sb sc n a negA double HNeg HDouble PDouble)as PA.
  exact(full_source_AllI M b c n a all sb sc(ex_intro _ k(conj BAll BC))PA HShift HAll).
Qed.

Theorem source_full_not_ex_neg_from_all M b c n a negA exNeg notEx all k:
  context_bounded M b c n k ->source_bounded M a(succM M k) ->
  sf_relation M SFImpl a(zeroM M)negA ->sf_relation M SFEx negA(zeroM M)exNeg ->
  sf_relation M SFImpl exNeg(zeroM M)notEx ->sf_relation M SFAll a(zeroM M)all ->
  source_full_prv M b c n all ->source_full_prv M b c n notEx.
Proof.
  intros BC BA HNeg HEx HNot HAll PAll.
  pose proof(proj2(source_bounded_accept_binary M SFImpl a(zeroM M)negA(succM M k)
    (or_intror(or_intror eq_refl))HNeg)(conj BA(source_bounded_accept_falsity M(succM M k))))as BNeg.
  pose proof(proj2(source_bounded_accept_unary M SFEx negA exNeg k(or_intror eq_refl)HEx)BNeg)as BEx.
  pose proof(proj2(source_bounded_accept_binary M SFImpl exNeg(zeroM M)notEx k
    (or_intror(or_intror eq_refl))HNot)(conj BEx(source_bounded_accept_falsity M k)))as BNot.
  destruct(environment_cons_total M b c n exNeg)as(db&dc&dn&HConsD).
  pose proof(proj2(context_bounded_cons M b c n exNeg db dc dn k HConsD)(conj BEx BC))as BD.
  pose proof(source_full_cons_head M b c n exNeg db dc dn k HConsD BEx BD)as PEx.
  pose proof(source_full_cons_weaken M b c n exNeg db dc dn k all HConsD BD PAll)as PAllD.
  destruct(context_shift_total M db dc dn)as(sb&sc&HShift).
  pose proof(context_shift_preserves_bound M db dc dn sb sc k HShift BD)as BS.
  pose proof(source_full_all_shift M db dc dn a all sb sc HAll PAllD HShift)as PAS.
  destruct(environment_cons_total M sb sc dn negA)as(ub&uc&un&HConsU).
  pose proof(proj2(context_bounded_cons M sb sc dn negA ub uc un(succM M k)HConsU)(conj BNeg BS))as BU.
  pose proof(source_full_cons_weaken M sb sc dn negA ub uc un(succM M k)a HConsU BU PAS)as PA.
  pose proof(source_full_cons_head M sb sc dn negA ub uc un(succM M k)HConsU BNeg BU)as PNeg.
  pose proof(source_full_modus_ponens M ub uc un a(zeroM M)negA HNeg PNeg PA)as PFalseU.
  assert(HFalseShift:source_formula_shift M(zeroM M)(zeroM M)).
  { apply(proj2(numerical_renaming_invalid M(zeroM M)(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)(zeroM M)(or_introl eq_refl))). reflexivity. }
  pose proof(full_source_ExE M db dc dn negA exNeg(zeroM M)(zeroM M)sb sc ub uc un
    (ex_intro _ k(conj(source_bounded_accept_falsity M k)BD))PEx PFalseU HEx HShift HConsU HFalseShift)as PFalse.
  exact(full_source_II M b c n exNeg(zeroM M)notEx db dc dn(ex_intro _ k(conj BNot BC))PFalse HConsD HNot).
Qed.
Print Assumptions source_full_all_from_not_ex_neg.
Print Assumptions source_full_not_ex_neg_from_all.
