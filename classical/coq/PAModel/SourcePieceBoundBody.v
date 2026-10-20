(** Explicit named witness bodies for the outer ExE shells of PCf bounds. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalRenamingMaps NumericalRenaming NumericalInstantiation SourceDomainInstances SourceDomainInstanceRenaming
  SourceOrdinalPredicate SourcePieceConjunction SourcePieceConjunctionBounds SourcePieceConjunctionRenaming SourcePieceBoundGoal.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Definition source_pcf_bound_body M domain level sb sc n g X d body:=exists ordinal member pc left,
  numerical_instantiation M(source_ordinal_predicate_code M)d ordinal /\sf_relation M SFMember g d member /\
  source_piece_conjunction M domain level sb sc n d X pc /\sf_relation M SFAnd ordinal member left /\sf_relation M SFAnd left pc body.

Theorem source_pcf_bound_goal_body M domain level sb sc n g X goal:
  source_pcf_bound_goal M domain level sb sc n g X goal <->exists body,
    source_pcf_bound_body M domain level sb sc n(succM M g)(succM M X)(zeroM M)body /\
    sf_relation M SFEx body(zeroM M)goal.
Proof.
  split.
  - intros(pc&member&left&body&HPC&HM&HL&HB&HE).
    exists body. split;[|exact HE]. exists(source_ordinal_predicate_code M),member,pc,left.
    split;[apply source_domain_instance_zero,source_ordinal_predicate_bounded|]. auto.
  - intros(body&(ordinal&member&pc&left&HO&HM&HPC&HL&HB)&HE).
    pose proof(numerical_instantiation_functional M(source_ordinal_predicate_code M)(zeroM M)ordinal
      (source_ordinal_predicate_code M)HO(source_domain_instance_zero M _ (source_ordinal_predicate_bounded M))) as E.
    subst ordinal. exists pc,member,left,body. auto.
Qed.

Theorem source_pcf_bound_body_renaming M domain level sb sc n g X d f rb rc rn delta h Y e out:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
  source_piece_table_valid M sb sc n ->source_pcf_bound_body M domain level sb sc n g X d f ->
  numerical_renaming M f rb rc rn delta out ->renaming_lookup M rb rc rn delta g h ->
  renaming_lookup M rb rc rn delta X Y ->renaming_lookup M rb rc rn delta d e ->
  source_pcf_bound_body M domain level sb sc n h Y e out.
Proof.
  intros HD HL HV(ordinal&member&pc&left&HO&HM&HPC&HLeft&HBody)HR HG HX HDE.
  destruct(proj1(numerical_renaming_binary M SFAnd left pc f rb rc rn delta out(or_introl eq_refl)HBody)HR)
    as(left'&pc'&HRleft&HRpc&HBody').
  destruct(proj1(numerical_renaming_binary M SFAnd ordinal member left rb rc rn delta left'(or_introl eq_refl)HLeft)HRleft)
    as(ordinal'&member'&HRO&HRM&HLeft').
  pose proof(source_domain_instance_renaming M(source_ordinal_predicate_code M)d ordinal rb rc rn delta ordinal' e
    (source_ordinal_predicate_bounded M)HO HRO HDE) as HO'.
  pose proof(source_piece_conjunction_renaming M n domain level sb sc d X pc rb rc rn delta e Y pc'
    HD HL HV HPC HRpc HDE HX) as HPC'.
  destruct(proj1(numerical_renaming_member M g d member rb rc rn delta member' HM)HRM) as(u&v&HU&HV'&HM').
  pose proof(renaming_lookup_functional M rb rc rn delta g u h HU HG) as E. subst u.
  pose proof(renaming_lookup_functional M rb rc rn delta d v e HV' HDE) as E. subst v.
  exists ordinal',member',pc',left'. auto.
Qed.

Print Assumptions source_pcf_bound_goal_body.
Print Assumptions source_pcf_bound_body_renaming.
