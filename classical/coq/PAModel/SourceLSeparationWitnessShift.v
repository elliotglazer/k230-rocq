(** The external hierarchy-carrier slot is removed by the genuine source
    shift, rather than an assumed matrix-correspondence premise. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetSchemaConstructors SourceBounded
  SourceFunctionalityShells SourceCutoffShiftConstructors SourceCutoffPropositional SourceCutoffQuantifiers SourceFiniteCutoffShift
  SourceLDefinableProfile SourceLSeparationCarrierShell SourceQuantifierRules.
Unset Implicit Arguments.

Definition E_L_indexed_separation domain lp (selected:nat) :=E_sf SFEx(E_sf SFAnd domain(E_sf SFAll(E_sf SFImpl domain
  (E_sf_iff(E_sf SFMember(CEconst 0)(CEconst 1))(E_sf SFAnd(E_sf SFMember(CEconst 0)(CEconst selected))lp)))(CEconst 0)))(CEconst 0).
Definition E_L_canonical_separation_witness domain lp :=E_L_indexed_separation domain lp 2.
Definition source_lsep_indexed_shell M domain lp selected out :=exists zx za rhs lr rl point guarded all body,
  sf_relation M SFMember(zeroM M)(code_numeral M 1)zx /\sf_relation M SFMember(zeroM M)(code_numeral M selected)za /\
  sf_relation M SFAnd za lp rhs /\sf_relation M SFImpl zx rhs lr /\sf_relation M SFImpl rhs zx rl /\
  sf_relation M SFAnd lr rl point /\sf_relation M SFImpl domain point guarded /\sf_relation M SFAll guarded(zeroM M)all /\
  sf_relation M SFAnd domain all body /\sf_relation M SFEx body(zeroM M)out.

Theorem source_lsep_indexed_split M domain lp selected out :
  code_relation M(L_definable_profile_environment lp domain)(E_L_indexed_separation(CEvar 1)(CEvar 0)selected)out ->
  source_lsep_indexed_shell M domain lp selected out.
Proof.
  intro HGraph.
  destruct(sf_relation_total M SFMember(zeroM M)(code_numeral M 1)) as(zx&HZX).
  destruct(sf_relation_total M SFMember(zeroM M)(code_numeral M selected)) as(za&HZA).
  destruct(sf_relation_total M SFAnd za lp) as(rhs&HRhs).
  destruct(sf_relation_total M SFImpl zx rhs) as(lr&HLR).
  destruct(sf_relation_total M SFImpl rhs zx) as(rl&HRL).
  destruct(sf_relation_total M SFAnd lr rl) as(point&HPoint).
  destruct(sf_relation_total M SFImpl domain point) as(guarded&HGuard).
  destruct(sf_relation_total M SFAll guarded(zeroM M)) as(all&HAll).
  destruct(sf_relation_total M SFAnd domain all) as(body&HBody).
  destruct(sf_relation_total M SFEx body(zeroM M)) as(other&HOther).
  assert(HOtherGraph:code_relation M(L_definable_profile_environment lp domain)
    (E_L_indexed_separation(CEvar 1)(CEvar 0)selected)other).
  { unfold E_L_indexed_separation,L_definable_profile_environment,E_sf_iff. functionality_graph. }
  pose proof(code_relation_functional M _ _ out other HGraph HOtherGraph) as E. subst other.
  exists zx,za,rhs,lr,rl,point,guarded,all,body. repeat first[assumption|split].
Qed.

Theorem source_L_separation_witness_carrier_shift M domain lp shifted old out :
  source_bounded M domain(code_numeral M 1) ->source_cutoff_shift M 2 lp shifted ->
  code_relation M(L_definable_profile_environment lp domain)(E_L_canonical_separation_witness(CEvar 1)(CEvar 0))old ->
  code_relation M(L_definable_profile_environment shifted domain)(E_L_carrier_separation(CEvar 1)(CEvar 0))out ->
  source_formula_shift M old out.
Proof.
  intros HD HLP HOld HOut.
  destruct(source_lsep_indexed_split M domain lp 2 old HOld)
    as(zx&za&rhs&lr&rl&point&guarded&all&body&HZX&HZA&HRhs&HLR&HRL&HPoint&HGuard&HAll&HBody&HEx).
  destruct(source_lsep_indexed_split M domain shifted 3 out HOut)
    as(zx'&za'&rhs'&lr'&rl'&point'&guarded'&all'&body'&HZX'&HZA'&HRhs'&HLR'&HRL'&HPoint'&HGuard'&HAll'&HBody'&HEx').
  pose proof(sf_relation_functional M SFMember(zeroM M)(code_numeral M 1)zx zx' HZX HZX') as E. subst zx'.
  pose proof(source_cutoff_shift_fixed_member M 2 0 1 zx zx HZX HZX) as HZXShift.
  pose proof(source_cutoff_shift_fixed_member M 2 0 2 za za' HZA HZA') as HZAShift.
  pose proof(source_cutoff_shift_binary M 2 SFAnd za lp rhs za' shifted rhs'(or_introl eq_refl)HRhs HRhs' HZAShift HLP) as HRhsShift.
  pose proof(source_cutoff_shift_binary M 2 SFImpl zx rhs lr zx rhs' lr'(or_intror(or_intror eq_refl))HLR HLR' HZXShift HRhsShift) as HLRShift.
  pose proof(source_cutoff_shift_binary M 2 SFImpl rhs zx rl rhs' zx rl'(or_intror(or_intror eq_refl))HRL HRL' HRhsShift HZXShift) as HRLShift.
  pose proof(source_cutoff_shift_binary M 2 SFAnd lr rl point lr' rl' point'(or_introl eq_refl)HPoint HPoint' HLRShift HRLShift) as HPointShift.
  pose proof(source_cutoff_shift_binary M 2 SFImpl domain point guarded domain point' guarded'(or_intror(or_intror eq_refl))HGuard HGuard'
    (source_cutoff_shift_fixes_domain M 1 domain HD)HPointShift) as HGuardShift.
  pose proof(source_cutoff_quantifier_join M 1 true guarded guarded' all all' HAll HAll' HGuardShift) as HAllShift.
  pose proof(source_cutoff_shift_binary M 1 SFAnd domain all body domain all' body'(or_introl eq_refl)HBody HBody'
    (source_cutoff_shift_fixes_domain M 0 domain HD)HAllShift) as HBodyShift.
  exact(source_cutoff_zero_is_shift M old out(source_cutoff_quantifier_join M 0 false body body' old out HEx HEx' HBodyShift)).
Qed.
Print Assumptions source_lsep_indexed_split.
Print Assumptions source_L_separation_witness_carrier_shift.
