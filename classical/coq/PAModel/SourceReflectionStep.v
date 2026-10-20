(** The exact least-Cond ordinal-step relation with arbitrary named input
    x and ordinal output y. Only the quotient-free source syntax is used. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
  NumericalInstantiation NumericalSubstitutionMaps NumericalSubstitution NumericalRenamingMaps NumericalRenaming RenamingSubstitution
  SourceDomainInstances SourceUnarySubstitution SourceOrdinalPredicate SourcePieceConjunctionBounds
  SourceReflectionCondition SourceReflectionConditionBounds SourceReflectionConditionTransport SourceRelativizationBounds.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Definition source_reflection_step M domain level sb sc n x y out:=
  exists ordinal condition candidate member neg point all both,
    numerical_instantiation M(source_ordinal_predicate_code M)y ordinal /\
    source_reflection_condition M domain level(source_ordinal_predicate_code M)sb sc n x y condition /\
    source_reflection_condition M domain level(source_ordinal_predicate_code M)sb sc n(succM M x)(zeroM M)candidate /\
    sf_relation M SFMember(zeroM M)(succM M y)member /\sf_relation M SFImpl candidate(zeroM M)neg /\
    sf_relation M SFImpl member neg point /\sf_relation M SFAll point(zeroM M)all /\
    sf_relation M SFAnd ordinal condition both /\sf_relation M SFAnd both all out.

Theorem source_reflection_step_total M domain level sb sc n x y:
  exists out,source_reflection_step M domain level sb sc n x y out.
Proof.
  destruct(numerical_instantiation_total M(source_ordinal_predicate_code M)y) as(ordinal&HO).
  destruct(source_reflection_condition_total M domain level(source_ordinal_predicate_code M)sb sc n x y) as(condition&HC).
  destruct(source_reflection_condition_total M domain level(source_ordinal_predicate_code M)sb sc n(succM M x)(zeroM M)) as(candidate&HCA).
  destruct(sf_relation_total M SFMember(zeroM M)(succM M y)) as(member&HM).
  destruct(sf_relation_total M SFImpl candidate(zeroM M)) as(neg&HN).
  destruct(sf_relation_total M SFImpl member neg) as(point&HP).
  destruct(sf_relation_total M SFAll point(zeroM M)) as(all&HA).
  destruct(sf_relation_total M SFAnd ordinal condition) as(both&HB).
  destruct(sf_relation_total M SFAnd both all) as(out&HF).
  exists out,ordinal,condition,candidate,member,neg,point,all,both. auto 12.
Qed.

Theorem source_reflection_step_functional M domain level sb sc n x y a b:
  source_reflection_step M domain level sb sc n x y a ->source_reflection_step M domain level sb sc n x y b ->a=b.
Proof.
  intros(o&c&ca&m&ne&p&al&bo&HO&HC&HCA&HM&HN&HP&HA&HB&HF)
    (o'&c'&ca'&m'&ne'&p'&al'&bo'&HO'&HC'&HCA'&HM'&HN'&HP'&HA'&HB'&HF').
  pose proof(numerical_instantiation_functional M(source_ordinal_predicate_code M)y o' o HO' HO) as E. subst o'.
  pose proof(source_reflection_condition_functional M domain level(source_ordinal_predicate_code M)sb sc n x y c' c HC' HC) as E. subst c'.
  pose proof(source_reflection_condition_functional M domain level(source_ordinal_predicate_code M)sb sc n(succM M x)(zeroM M)ca' ca HCA' HCA) as E. subst ca'.
  assert(E:m'=m) by(eapply sf_relation_functional;eassumption). subst m'.
  assert(E:ne'=ne) by(eapply sf_relation_functional;eassumption). subst ne'.
  assert(E:p'=p) by(eapply sf_relation_functional;eassumption). subst p'.
  assert(E:al'=al) by(eapply sf_relation_functional;eassumption). subst al'.
  assert(E:bo'=bo) by(eapply sf_relation_functional;eassumption). subst bo'.
  exact(sf_relation_functional M SFAnd bo al a b HF HF').
Qed.

Theorem source_reflection_step_bounded M domain level sb sc n x y out k:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc n ->
  coding_lt M x k ->coding_lt M y k ->source_reflection_step M domain level sb sc n x y out ->source_bounded M out k.
Proof.
  intros HD HL HV HX HY(o&c&ca&m&ne&p&al&bo&HO&HC&HCA&HM&HN&HP&HA&HB&HF).
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)y o k(source_ordinal_predicate_bounded M)HY HO) as BO.
  pose proof(source_reflection_condition_bounded M domain level(source_ordinal_predicate_code M)sb sc n x y c k
    HD HL(source_ordinal_predicate_bounded M)HV HX HY HC) as BC.
  pose proof(source_reflection_condition_bounded M domain level(source_ordinal_predicate_code M)sb sc n(succM M x)(zeroM M)ca(succM M k)
    HD HL(source_ordinal_predicate_bounded M)HV(proj2(coding_lt_succ_cancel M x k)HX)(coding_zero_lt_succ M k)HCA) as BCA.
  pose proof(proj2(source_bounded_accept_atom M SFMember(zeroM M)(succM M y)m(succM M k)(or_introl eq_refl)HM)
    (conj(coding_zero_lt_succ M k)(proj2(coding_lt_succ_cancel M y k)HY))) as BM.
  pose proof(proj2(source_bounded_accept_binary M SFImpl ca(zeroM M)ne(succM M k)(or_intror(or_intror eq_refl))HN)
    (conj BCA(source_bounded_accept_falsity M(succM M k)))) as BN.
  pose proof(proj2(source_bounded_accept_binary M SFImpl m ne p(succM M k)(or_intror(or_intror eq_refl))HP)(conj BM BN)) as BP.
  pose proof(proj2(source_bounded_accept_unary M SFAll p al k(or_introl eq_refl)HA)BP) as BA.
  pose proof(proj2(source_bounded_accept_binary M SFAnd o c bo k(or_introl eq_refl)HB)(conj BO BC)) as BB.
  exact(proj2(source_bounded_accept_binary M SFAnd bo al out k(or_introl eq_refl)HF)(conj BB BA)).
Qed.

Theorem source_reflection_step_substitution M domain level sb sc n x y f rb rc rn base u v out:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc n ->
  source_reflection_step M domain level sb sc n x y f ->numerical_substitution M f rb rc rn base out ->
  substitution_lookup M rb rc rn base x u ->substitution_lookup M rb rc rn base y v ->
  source_reflection_step M domain level sb sc n u v out.
Proof.
  intros HD HL HV(o&c&ca&m&ne&p&al&bo&HO&HC&HCA&HM&HN&HP&HA&HB&HF)HR HX HY.
  destruct(proj1(numerical_substitution_binary M SFAnd bo al f rb rc rn base out(or_introl eq_refl)HF)HR)
    as(bo'&al'&HRB&HRA&HF').
  destruct(proj1(numerical_substitution_binary M SFAnd o c bo rb rc rn base bo'(or_introl eq_refl)HB)HRB)
    as(o'&c'&HRO&HRC&HB').
  pose proof(source_domain_instance_substitution M(source_ordinal_predicate_code M)y o rb rc rn base o' v
    (source_ordinal_predicate_bounded M)HO HRO HY) as HO'.
  pose proof(source_reflection_condition_substitution M domain level(source_ordinal_predicate_code M)sb sc n x y c rb rc rn base u v c'
    HD HL(source_ordinal_predicate_bounded M)HV HC HRC HX HY) as HC'.
  destruct(proj1(numerical_substitution_quantifier M true p al rb rc rn base al' HA)HRA)
    as(ab&ac&an&p'&HMap&HRP&HA').
  destruct(proj1(numerical_substitution_binary M SFImpl m ne p ab ac an(succM M base)p'(or_intror(or_intror eq_refl))HP)HRP)
    as(m'&ne'&HRM&HRN&HP').
  destruct(proj1(numerical_substitution_binary M SFImpl ca(zeroM M)ne ab ac an(succM M base)ne'(or_intror(or_intror eq_refl))HN)HRN)
    as(ca'&z&HRCA&HRZ&HN').
  apply(proj1(numerical_substitution_invalid M(zeroM M)ab ac an(succM M base)z(or_introl eq_refl))) in HRZ. subst z.
  pose proof(source_reflection_condition_substitution M domain level(source_ordinal_predicate_code M)sb sc n(succM M x)(zeroM M)ca
    ab ac an(succM M base)(succM M u)(zeroM M)ca' HD HL(source_ordinal_predicate_bounded M)HV HCA HRCA
    (proj2(proj2 HMap)x u HX)(proj1(proj2 HMap))) as HCA'.
  destruct(proj1(numerical_substitution_member M(zeroM M)(succM M y)m ab ac an(succM M base)m' HM)HRM)
    as(i&j&HI&HJ&HM').
  pose proof(substitution_lookup_functional M ab ac an(succM M base)(zeroM M)i(zeroM M)HI(proj1(proj2 HMap))) as E. subst i.
  pose proof(substitution_lookup_functional M ab ac an(succM M base)(succM M y)j(succM M v)HJ(proj2(proj2 HMap)y v HY)) as E. subst j.
  exists o',c',ca',m',ne',p',al',bo'. auto 12.
Qed.

Print Assumptions source_reflection_step_total.
Print Assumptions source_reflection_step_functional.
Print Assumptions source_reflection_step_bounded.
Print Assumptions source_reflection_step_substitution.
