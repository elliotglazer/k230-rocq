(** Literal witness_closed and matrix_request syntax with arbitrary
    predicate codes, parameter tails and container/input names. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
  SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds SourcePropositionalRebase
  SourceWFSeparationConstructor NumericalRenaming NumericalSubstitution SourceRoleReopening.
Unset Implicit Arguments.

Definition E_upper_matrix_request mat b :=
  E_sf SFImpl (E_sf_ex mat)
    (E_sf_ex (E_sf SFAnd (E_sf SFMember (CEconst 0) (CEadd b (CEconst 1))) mat)).
Definition E_upper_witness_closed mat b :=
  E_sf_all (E_sf SFImpl (E_sf SFMember (CEconst 0) (CEadd b (CEconst 1)))
    (E_sf SFImpl (E_sf_ex mat)
      (E_sf_ex (E_sf SFAnd (E_sf SFMember (CEconst 0) (CEadd b (CEconst 2))) mat)))).

Definition source_upper_witness_closed_recipe M phi delta b out := exists mat,
  numerical_renaming M phi (code_numeral M 4) (code_numeral M 1)
    (code_numeral M 2) delta mat /\
  code_relation M (schema_env3 mat b b)
    (E_upper_witness_closed (CEvar 0) (CEvar 1)) out.
Definition source_upper_matrix_request_recipe M phi delta p b out := exists rb rc mat,
  source_role_reopening M (succM M p) (zeroM M) rb rc /\
  numerical_substitution M phi rb rc (code_numeral M 2) (succM M delta) mat /\
  code_relation M (schema_env3 mat b b)
    (E_upper_matrix_request (CEvar 0) (CEvar 1)) out.

Theorem source_upper_witness_closed_total M phi delta b :
  exists out,source_upper_witness_closed_recipe M phi delta b out.
Proof.
  destruct (numerical_renaming_total M phi (code_numeral M 4) (code_numeral M 1)
    (code_numeral M 2) delta) as [mat HM].
  destruct (code_relation_total M (E_upper_witness_closed (CEvar 0) (CEvar 1))
    (schema_env3 mat b b)) as [out HO].
  exists out,mat. auto.
Qed.

Theorem source_upper_matrix_request_total M phi delta p b :
  exists out,source_upper_matrix_request_recipe M phi delta p b out.
Proof.
  destruct (source_role_reopening_total M (succM M p) (zeroM M)) as [rb [rc HR]].
  destruct (numerical_substitution_total M phi rb rc (code_numeral M 2) (succM M delta)) as [mat HM].
  destruct (code_relation_total M (E_upper_matrix_request (CEvar 0) (CEvar 1))
    (schema_env3 mat b b)) as [out HO].
  exists out,rb,rc,mat. auto.
Qed.

Lemma source_name_plus_one_graph M mat b :
  code_relation M (schema_env3 mat b b) (CEadd (CEvar 1) (CEconst 1)) (succM M b).
Proof.
  exists b,(code_numeral M 1). split;[reflexivity|]. split;[reflexivity|].
  apply Arithmetic.succ_as_add.
Qed.
Lemma source_name_plus_two_graph M mat b :
  code_relation M (schema_env3 mat b b) (CEadd (CEvar 1) (CEconst 2)) (succM M (succM M b)).
Proof.
  exists b,(code_numeral M 2). split;[reflexivity|]. split;[reflexivity|].
  rewrite Arithmetic.add_comm. cbn [code_numeral].
  now rewrite !Arithmetic.add_succ,Arithmetic.add_zero.
Qed.

Theorem source_upper_matrix_request_shell M mat b out :
  code_relation M (schema_env3 mat b b)
    (E_upper_matrix_request (CEvar 0) (CEvar 1)) out ->
  exists member pair some bounded,
    sf_relation M SFMember (zeroM M) (succM M b) member /\
    sf_relation M SFAnd member mat pair /\
    sf_relation M SFEx mat (zeroM M) some /\
    sf_relation M SFEx pair (zeroM M) bounded /\sf_relation M SFImpl some bounded out.
Proof.
  intro HO. destruct (schema_expression_split M _ SFImpl _ _ out HO)
    as [some [bounded [HSome [HBound HImpl]]]].
  destruct (schema_expression_quantifier_split M _ SFEx _ some HSome) as [mat' [HMat' HEx]].
  change (mat'=mat) in HMat'. subst mat'.
  destruct (schema_expression_quantifier_split M _ SFEx _ bounded HBound) as [pair [HPair HExBound]].
  destruct (schema_expression_split M _ SFAnd _ _ pair HPair) as [member [mat' [HMem [HMat' HAnd]]]].
  change (mat'=mat) in HMat'. subst mat'.
  exists member,pair,some,bounded. split;[|auto].
  exact (proj1 (schema_expression_graph M (schema_env3 mat b b) SFMember
    (CEconst 0) (CEadd (CEvar 1) (CEconst 1)) (zeroM M) (succM M b) member
    eq_refl (source_name_plus_one_graph M mat b)) HMem).
Qed.

Theorem source_upper_witness_closed_shell M mat b out :
  code_relation M (schema_env3 mat b b)
    (E_upper_witness_closed (CEvar 0) (CEvar 1)) out ->
  exists guard member pair some bounded request point,
    sf_relation M SFMember (zeroM M) (succM M b) guard /\
    sf_relation M SFMember (zeroM M) (succM M (succM M b)) member /\
    sf_relation M SFAnd member mat pair /\sf_relation M SFEx mat (zeroM M) some /\
    sf_relation M SFEx pair (zeroM M) bounded /\sf_relation M SFImpl some bounded request /\
    sf_relation M SFImpl guard request point /\sf_relation M SFAll point (zeroM M) out.
Proof.
  intro HO. destruct (schema_expression_quantifier_split M _ SFAll _ out HO)
    as [point [HPoint HAll]].
  destruct (schema_expression_split M _ SFImpl _ _ point HPoint)
    as [guard [request [HGuard [HRequest HPointImpl]]]].
  destruct (schema_expression_split M _ SFImpl _ _ request HRequest)
    as [some [bounded [HSome [HBound HImpl]]]].
  destruct (schema_expression_quantifier_split M _ SFEx _ some HSome) as [mat' [HMat' HEx]].
  change (mat'=mat) in HMat'. subst mat'.
  destruct (schema_expression_quantifier_split M _ SFEx _ bounded HBound) as [pair [HPair HExBound]].
  destruct (schema_expression_split M _ SFAnd _ _ pair HPair) as [member [mat' [HMem [HMat' HAnd]]]].
  change (mat'=mat) in HMat'. subst mat'.
  assert (HG:sf_relation M SFMember (zeroM M) (succM M b) guard).
  { exact (proj1 (schema_expression_graph M (schema_env3 mat b b) SFMember
      (CEconst 0) (CEadd (CEvar 1) (CEconst 1)) (zeroM M) (succM M b) guard
      eq_refl (source_name_plus_one_graph M mat b)) HGuard). }
  assert (HM:sf_relation M SFMember (zeroM M) (succM M (succM M b)) member).
  { exact (proj1 (schema_expression_graph M (schema_env3 mat b b) SFMember
      (CEconst 0) (CEadd (CEvar 1) (CEconst 2)) (zeroM M) (succM M (succM M b)) member
      eq_refl (source_name_plus_two_graph M mat b)) HMem). }
  exists guard,member,pair,some,bounded,request,point. repeat split;assumption.
Qed.

Print Assumptions source_upper_witness_closed_total.
Print Assumptions source_upper_matrix_request_total.
Print Assumptions source_upper_matrix_request_shell.
Print Assumptions source_upper_witness_closed_shell.
