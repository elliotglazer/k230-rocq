(** The specialized literal Separation axiom is exactly the canonical
    filtered profile at the two newly bound set variables. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SetSchemaConstructors SchemaConstructorBounds SourcePropositionalRebase
  SourceWFSeparationConstructor SourcePropositionalTemplates SourceFilteredMinimumPrograms
  SourceCanonicalFilteredMinimum SourceSeparationZeroSpecialization SourceSeparationSubset.
Unset Implicit Arguments.

Theorem source_separation_filter_shell M phi specialized :
  code_relation M (fun _=>phi) (E_separation_zero (CEvar 0)) specialized ->
  exists profile,sf_relation M SFEx profile (zeroM M) specialized /\
    code_relation M (canonical_filter_environment phi (zeroM M) (code_numeral M 1))
      canonical_filter_profile profile.
Proof.
  intro H. unfold E_separation_zero in H.
  destruct (schema_expression_quantifier_split M _ SFEx _ specialized H) as (profile&HP&HEx).
  destruct (schema_expression_quantifier_split M _ SFAll _ profile HP) as (point&HPoint&HAll).
  destruct (code_relation_total M (E_sf_mem 0 1) (fun _=>phi)) as (left&HL).
  destruct (code_relation_total M (E_sf_mem 0 2) (fun _=>phi)) as (right&HR).
  assert (HLeft:sf_relation M SFMember (zeroM M) (code_numeral M 1) left).
  { exact (proj1 (schema_expression_graph M (fun _=>phi) SFMember (CEconst 0) (CEconst 1)
      (zeroM M) (code_numeral M 1) left eq_refl eq_refl) HL). }
  assert (HRight:sf_relation M SFMember (zeroM M) (code_numeral M 2) right).
  { exact (proj1 (schema_expression_graph M (fun _=>phi) SFMember (CEconst 0) (CEconst 2)
      (zeroM M) (code_numeral M 2) right eq_refl eq_refl) HR). }
  assert (HPoint':code_relation M (schema_env3 left right phi)
    (source_prop_expression filtered_minimum_profile) point).
  { assert (HH:forall index,code_relation M (fun _=>phi)
       (match index with 0=>E_sf_mem 0 1|1=>E_sf_mem 0 2|_=>CEvar 0 end)
       (schema_env3 left right phi index)).
    { intros [|[|index]];cbn [schema_env3];try assumption;reflexivity. }
    exact (proj1 (source_prop_expression_with_graph M (fun _=>phi)
      (fun index=>match index with 0=>E_sf_mem 0 1|1=>E_sf_mem 0 2|_=>CEvar 0 end)
      (schema_env3 left right phi) filtered_minimum_profile HH point) HPoint). }
  destruct (code_relation_total M canonical_filter_profile
    (canonical_filter_environment phi (zeroM M) (code_numeral M 1))) as (profile'&HG).
  destruct (canonical_filter_profile_split M phi (zeroM M) (code_numeral M 1) profile' HG)
    as (point'&left'&right'&HAll'&HLeft'&HRight'&HPoint'').
  pose proof (sf_relation_functional M SFMember _ _ left' left HLeft' HLeft) as E.
  subst left'.
  pose proof (sf_relation_functional M SFMember _ _ right' right HRight' HRight) as E.
  subst right'.
  pose proof (code_relation_functional M _ (schema_env3 left right phi) point' point HPoint'' HPoint') as E.
  subst point'.
  pose proof (sf_relation_functional M SFAll _ _ profile' profile HAll' HAll) as E.
  subst profile'. exists profile. auto.
Qed.

Print Assumptions source_separation_filter_shell.
