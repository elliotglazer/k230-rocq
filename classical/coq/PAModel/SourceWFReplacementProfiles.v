(** Exact raw and WF-range profiles at the same Replacement output set. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SetSchemaConstructors SourceWFFormula NumericalWFFoundation SourceNumeralLift.
From Undecidability.FOL Require Import Sets.minZF.
Unset Implicit Arguments.
Open Scope minZFsyn.

Definition source_wf_domain1_code M := code_numeral M (sf_encode (wf_class $1)).
Definition E_wf_rep_raw_profile d d1 theta :=
  E_sf_all (E_sf_iff (E_sf_mem 0 1) (E_sf_ex
    (E_sf SFAnd (E_sf_mem 0 3) (E_sf SFAnd (E_sf SFAnd d d1) theta)))).
Definition E_wf_rep_target_profile d theta :=
  E_sf_all (E_sf SFImpl d (E_sf_iff (E_sf_mem 0 1)
    (E_sf_ex (E_sf SFAnd d (E_sf SFAnd (E_sf_mem 0 3) theta))))).
Definition wf_rep_profile_env M theta := schema_env3 (source_wf_domain_code M) (source_wf_domain1_code M) theta.
Definition source_wf_rep_raw_profile_graph M theta profile :=
  code_relation M (wf_rep_profile_env M theta)
    (E_wf_rep_raw_profile (CEvar 0) (CEvar 1) (CEvar 2)) profile.
Definition source_wf_rep_target_profile_graph M theta profile :=
  code_relation M (wf_rep_profile_env M theta)
    (E_wf_rep_target_profile (CEvar 0) (CEvar 2)) profile.

Print Assumptions source_wf_rep_raw_profile_graph.
Print Assumptions source_wf_rep_target_profile_graph.
