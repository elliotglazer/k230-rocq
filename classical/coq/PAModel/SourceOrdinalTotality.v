(** Exact outer totality premise of ordinal collection and its fresh-variable
    transport. The arbitrary Q matrix is never decoded. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes
  NumericalRenaming RenamingSubstitution NumericalSubstitution NumericalSubstitutionMaps
  SourceOrdinalPredicate SourceFiniteCutoffShift SourceCutoffQuantifiers SourceQfFunctionality
  SourceSubstitutionIdentity SourceDomainInstances SourceQuantifierRules SourceCutoffShiftCommutation.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Definition source_oc_totality_graph M phi x total :=exists phiV phiD body ex input point,
  source_cutoff_shift M 2 phi phiV /\source_cutoff_shift M 2 phiV phiD /\
  sf_relation M SFAnd(source_ordinal_predicate_code M) phiD body /\
  sf_relation M SFEx body(zeroM M) ex /\sf_relation M SFMember(zeroM M)(succM M x) input /\
  sf_relation M SFImpl input ex point /\sf_relation M SFAll point(zeroM M) total.

Theorem source_oc_totality_total M phi x :exists total,source_oc_totality_graph M phi x total.
Proof.
  destruct(source_cutoff_shift_total M 2 phi) as (phiV&HV).
  destruct(source_cutoff_shift_total M 2 phiV) as (phiD&HD).
  destruct(sf_relation_total M SFAnd(source_ordinal_predicate_code M) phiD) as (body&HB).
  destruct(sf_relation_total M SFEx body(zeroM M)) as (ex&HE).
  destruct(sf_relation_total M SFMember(zeroM M)(succM M x)) as (input&HI).
  destruct(sf_relation_total M SFImpl input ex) as (point&HP).
  destruct(sf_relation_total M SFAll point(zeroM M)) as (total&HT).
  exists total,phiV,phiD,body,ex,input,point. repeat split;assumption.
Qed.

Theorem source_oc_totality_functional M phi x a b :
  source_oc_totality_graph M phi x a ->source_oc_totality_graph M phi x b ->a=b.
Proof.
  intros(v&d&body&ex&input&point&HV&HD&HB&HE&HI&HP&HT)
    (v'&d'&body'&ex'&input'&point'&HV'&HD'&HB'&HE'&HI'&HP'&HT').
  pose proof(source_cutoff_shift_functional M 2 phi v v' HV HV') as E. subst v'.
  pose proof(source_cutoff_shift_functional M 2 v d d' HD HD') as E. subst d'.
  pose proof(sf_relation_functional M SFAnd _ _ body body' HB HB') as E. subst body'.
  pose proof(sf_relation_functional M SFEx _ _ ex ex' HE HE') as E. subst ex'.
  pose proof(sf_relation_functional M SFMember _ _ input input' HI HI') as E. subst input'.
  pose proof(sf_relation_functional M SFImpl _ _ point point' HP HP') as E. subst point'.
  exact(sf_relation_functional M SFAll _ _ a b HT HT').
Qed.

Theorem source_oc_totality_shift M phi phi' x total total' :
  source_oc_totality_graph M phi x total ->source_cutoff_shift M 2 phi phi' ->
  source_formula_shift M total total' ->source_oc_totality_graph M phi'(succM M x) total'.
Proof.
  intros(phiV&phiD&body&ex&input&point&HV&HD&HB&HE&HI&HP&HT) HPS HShift.
  pose proof(source_cutoff_shift_functional M 2 phi phiV phi' HV HPS) as E. subst phiV.
  assert(HC0:source_cutoff_shift M 0 total total').
  { exists(zeroM M),(zeroM M),(zeroM M). split;[repeat split;reflexivity|].
    apply(proj1(numerical_renaming_substitution M total(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1) total')) in HShift.
    rewrite Arithmetic.add_zero in HShift. exact HShift. }
  destruct(source_cutoff_quantifier_inv M 0 true point total total' HT HC0)
    as(point'&HT'&sb&sc&sn&HM&HS).
  apply(proj1(numerical_substitution_binary M SFImpl input ex point sb sc sn(code_numeral M 2) point'
    (or_intror(or_intror eq_refl)) HP)) in HS.
  destruct HS as(input'&ex'&HSI&HSE&HP').
  assert(HInput':sf_relation M SFMember(zeroM M)(succM M(succM M x)) input').
  { apply(proj1(numerical_substitution_member M _ _ input sb sc sn(code_numeral M 2) input' HI)) in HSI.
    destruct HSI as(u&v&HU&HV0&HInput).
    pose proof(substitution_lookup_functional M _ _ _ _ _ u _ HU
      (source_cutoff_shift_map_fixed_lookup M 1 sb sc sn HM 0)) as E. subst u.
    pose proof(substitution_lookup_functional M _ _ _ _ _ v _ HV0
      (source_cutoff_shift_map_tail_lookup M 1 sb sc sn x HM)) as E. now subst v. }
  assert(HExShift:source_cutoff_shift M 1 ex ex') by(exists sb,sc,sn;auto).
  destruct(source_cutoff_quantifier_inv M 1 false body ex ex' HE HExShift)
    as(body'&HE'&rb&rc&rn&HRM&HBody).
  apply(proj1(numerical_substitution_binary M SFAnd(source_ordinal_predicate_code M) phiD body
    rb rc rn(code_numeral M 3) body'(or_introl eq_refl) HB)) in HBody.
  destruct HBody as(ord'&phiD'&HSO&HSD&HB').
  assert(HOrdSelf:numerical_substitution M(source_ordinal_predicate_code M) rb rc rn(code_numeral M 3)
    (source_ordinal_predicate_code M)).
  { apply(numerical_substitution_identity_on_bound M _ rb rc rn(code_numeral M 3)(code_numeral M 1)
      (source_ordinal_predicate_bounded M)). intros i HBound. rewrite(domain_index_below_one M i HBound).
    exact(source_cutoff_shift_map_fixed_lookup M 2 rb rc rn HRM 0). }
  pose proof(numerical_substitution_functional M(source_ordinal_predicate_code M) rb rc rn(code_numeral M 3)
    ord'(source_ordinal_predicate_code M) HSO HOrdSelf) as E. subst ord'.
  exists phiD,phiD',body',ex',input',point'. split;[exact HD|].
  split;[exists rb,rc,rn;auto|]. repeat split;assumption.
Qed.

Print Assumptions source_oc_totality_total.
Print Assumptions source_oc_totality_functional.
Print Assumptions source_oc_totality_shift.
