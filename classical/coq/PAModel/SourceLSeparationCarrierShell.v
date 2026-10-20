(** Literal carrier/Y0, selected-set/A1 shell used by L Separation. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetSchemaConstructors
  SourcePropositionalTemplates SourceFunctionalityShells SourceLDefinableProfile SourceLDefinableProfileCalibration
  SourceLSeparationPoint SourceLSeparationData.
Unset Implicit Arguments.

Definition E_L_carrier_reflection lp sp :=E_sf SFAll
  (E_sf SFImpl(E_sf SFMember(CEconst 0)(CEconst 2))(E_sf_iff lp sp))(CEconst 0).
Definition E_L_carrier_transitive :=E_sf SFAll(E_sf SFImpl
  (E_sf SFMember(CEconst 0)(CEconst 3))(E_sf SFMember(CEconst 0)(CEconst 2)))(CEconst 0).
Definition E_L_carrier_separation domain lp :=E_sf SFEx(E_sf SFAnd domain(E_sf SFAll(E_sf SFImpl domain
  (E_sf_iff(E_sf SFMember(CEconst 0)(CEconst 1))(E_sf SFAnd(E_sf SFMember(CEconst 0)(CEconst 3))lp)))(CEconst 0)))(CEconst 0).
Definition source_lsep_carrier_def_shell M domain sp defex :=exists zx zy za selected conjunction lr rl definition alld defbody,
  sf_relation M SFMember(zeroM M)(code_numeral M 1)zx /\sf_relation M SFMember(zeroM M)(code_numeral M 2)zy /\
  sf_relation M SFMember(zeroM M)(code_numeral M 3)za /\sf_relation M SFAnd za sp selected /\
  sf_relation M SFAnd zy selected conjunction /\sf_relation M SFImpl zx conjunction lr /\
  sf_relation M SFImpl conjunction zx rl /\sf_relation M SFAnd lr rl definition /\
  sf_relation M SFAll definition(zeroM M)alld /\sf_relation M SFAnd domain alld defbody /\sf_relation M SFEx defbody(zeroM M)defex.

Theorem source_lsep_selected_profile_shell M domain za sp selected defex :
  sf_relation M SFMember(zeroM M)(code_numeral M 3)za ->sf_relation M SFAnd za sp selected ->
  code_relation M(L_definable_profile_environment selected domain)(E_L_definable_profile(CEvar 0)(CEvar 1))defex ->
  source_lsep_carrier_def_shell M domain sp defex.
Proof.
  intros HZA HSelected HDef.
  destruct(sf_relation_total M SFMember(zeroM M)(code_numeral M 1)) as(zx&HZX).
  destruct(sf_relation_total M SFMember(zeroM M)(code_numeral M 2)) as(zy&HZY).
  destruct(sf_relation_total M SFAnd zy selected) as(conjunction&HConjunction).
  destruct(sf_relation_total M SFImpl zx conjunction) as(lr&HLR).
  destruct(sf_relation_total M SFImpl conjunction zx) as(rl&HRL).
  destruct(sf_relation_total M SFAnd lr rl) as(definition&HDefinition).
  destruct(sf_relation_total M SFAll definition(zeroM M)) as(alld&HAll).
  destruct(sf_relation_total M SFAnd domain alld) as(defbody&HBody).
  destruct(sf_relation_total M SFEx defbody(zeroM M)) as(other&HOther).
  pose proof(source_definable_profile_shell M domain selected zx zy conjunction lr rl definition alld defbody other
    HZX HZY HConjunction HLR HRL HDefinition HAll HBody HOther) as HOtherGraph.
  pose proof(code_relation_functional M _ _ defex other HDef HOtherGraph) as E. subst other.
  exists zx,zy,za,selected,conjunction,lr,rl,definition,alld,defbody. repeat first[assumption|split].
Qed.

Lemma source_lsep_carrier_definition_graph M domain sp defex lp :
  source_lsep_carrier_def_shell M domain sp defex ->exists zx zy za definition alld defbody,
    sf_relation M SFMember(zeroM M)(code_numeral M 1)zx /\sf_relation M SFMember(zeroM M)(code_numeral M 2)zy /\
    sf_relation M SFMember(zeroM M)(code_numeral M 3)za /\
    code_relation M(source_lsep_environment M zx zy za lp sp)(source_prop_expression lsep_definition_point)definition /\
    sf_relation M SFAll definition(zeroM M)alld /\sf_relation M SFAnd domain alld defbody /\sf_relation M SFEx defbody(zeroM M)defex.
Proof.
  intros(zx&zy&za&selected&conjunction&lr&rl&definition&alld&defbody&HZX&HZY&HZA&HS&HC&HLR&HRL&HD&HA&HB&HE).
  exists zx,zy,za,definition,alld,defbody. split;[exact HZX|]. split;[exact HZY|]. split;[exact HZA|]. split.
  - unfold source_lsep_environment,lsep_definition_point,lsep_iff,source_prop_expression. functionality_graph.
  - repeat first[assumption|split].
Qed.
Print Assumptions source_lsep_selected_profile_shell.
Print Assumptions source_lsep_carrier_definition_graph.
