(** Exact numerical components of the finite raw Collection clauses. *)
From PAModel Require Import Model FiniteCoding CodeDescent CodeExpressions NumericalProofs
 NumericalVacuitySteps NamedLeibnizSteps QuotationPayloads QuotationFixedSource SetFormulaCodes NamedExistential
 RawCollectionProfile RawClauseAlpha.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Theorem raw_support_clause_parts M t a c u v theta body :
  code_relation M (raw_clause_parameters M t a c u v theta) E_raw_support_clause body ->
  exists du ma child source exsource dv mc guard,
    membership_graph M t u du /\
    membership_graph M u a ma /\
    quotation_binary M SFAnd du ma child /\
    quotation_binary M SFAnd child theta source /\
    named_exists_graph M u source exsource /\
    membership_graph M t v dv /\
    membership_graph M v c mc /\
    quotation_binary M SFAnd dv mc guard /\
    implication_graph M guard exsource body.
Proof.
  intro HB;set (rho:=raw_clause_parameters M t a c u v theta).
  destruct (code_relation_total M (E_wel (CEvar 0) (CEvar 3)) rho) as [du G_du].
  destruct (code_relation_total M (E_wel (CEvar 3) (CEvar 1)) rho) as [ma G_ma].
  destruct (code_relation_total M (E_wa (E_wel (CEvar 0) (CEvar 3)) (E_wel (CEvar 3) (CEvar 1))) rho) as [child G_child].
  destruct (code_relation_total M (E_wa (E_wa (E_wel (CEvar 0) (CEvar 3)) (E_wel (CEvar 3) (CEvar 1))) (CEvar 5)) rho) as [source G_source].
  destruct (code_relation_total M (E_wex (CEvar 3) (E_wa (E_wa (E_wel (CEvar 0) (CEvar 3)) (E_wel (CEvar 3) (CEvar 1))) (CEvar 5))) rho) as [exsource G_exsource].
  destruct (code_relation_total M (E_wel (CEvar 0) (CEvar 4)) rho) as [dv G_dv].
  destruct (code_relation_total M (E_wel (CEvar 4) (CEvar 2)) rho) as [mc G_mc].
  destruct (code_relation_total M (E_wa (E_wel (CEvar 0) (CEvar 4)) (E_wel (CEvar 4) (CEvar 2))) rho) as [guard G_guard].
  exists du,ma,child,source,exsource,dv,mc,guard.
  split;[exact (proj1 (ns_atom_expression M rho false (CEvar 0) (CEvar 3) t u du eq_refl eq_refl) G_du)|].
  split;[exact (proj1 (ns_atom_expression M rho false (CEvar 3) (CEvar 1) u a ma eq_refl eq_refl) G_ma)|].
  split;[exact (proj1 (quotation_binary_substitution_graph M rho SFAnd (E_wel (CEvar 0) (CEvar 3)) (E_wel (CEvar 3) (CEvar 1)) du ma child G_du G_ma) G_child)|].
  split;[exact (proj1 (quotation_binary_substitution_graph M rho SFAnd (E_wa (E_wel (CEvar 0) (CEvar 3)) (E_wel (CEvar 3) (CEvar 1))) (CEvar 5) child theta source G_child eq_refl) G_source)|].
  split;[exact (proj1 (named_exists_expression M rho (CEvar 3) (E_wa (E_wa (E_wel (CEvar 0) (CEvar 3)) (E_wel (CEvar 3) (CEvar 1))) (CEvar 5)) u source exsource eq_refl G_source) G_exsource)|].
  split;[exact (proj1 (ns_atom_expression M rho false (CEvar 0) (CEvar 4) t v dv eq_refl eq_refl) G_dv)|].
  split;[exact (proj1 (ns_atom_expression M rho false (CEvar 4) (CEvar 2) v c mc eq_refl eq_refl) G_mc)|].
  split;[exact (proj1 (quotation_binary_substitution_graph M rho SFAnd (E_wel (CEvar 0) (CEvar 4)) (E_wel (CEvar 4) (CEvar 2)) dv mc guard G_dv G_mc) G_guard)|].
  exact (proj1 (expression_implication_iff M rho (E_wa (E_wel (CEvar 0) (CEvar 4)) (E_wel (CEvar 4) (CEvar 2))) (E_wex (CEvar 3) (E_wa (E_wa (E_wel (CEvar 0) (CEvar 3)) (E_wel (CEvar 3) (CEvar 1))) (CEvar 5))) guard exsource body G_guard G_exsource) HB).
Qed.


Theorem raw_coverage_clause_parts M t a c u v theta body :
  code_relation M (raw_clause_parameters M t a c u v theta) E_raw_coverage_clause body ->
  exists du ma guard dv mc rest source exsource hasbody has inner,
    membership_graph M t u du /\
    membership_graph M u a ma /\
    quotation_binary M SFAnd du ma guard /\
    membership_graph M t v dv /\
    membership_graph M v c mc /\
    quotation_binary M SFAnd mc theta rest /\
    quotation_binary M SFAnd dv rest source /\
    named_exists_graph M v source exsource /\
    quotation_binary M SFAnd dv theta hasbody /\
    named_exists_graph M v hasbody has /\
    implication_graph M has exsource inner /\
    implication_graph M guard inner body.
Proof.
  intro HB;set (rho:=raw_clause_parameters M t a c u v theta).
  destruct (code_relation_total M (E_wel (CEvar 0) (CEvar 3)) rho) as [du G_du].
  destruct (code_relation_total M (E_wel (CEvar 3) (CEvar 1)) rho) as [ma G_ma].
  destruct (code_relation_total M (E_wa (E_wel (CEvar 0) (CEvar 3)) (E_wel (CEvar 3) (CEvar 1))) rho) as [guard G_guard].
  destruct (code_relation_total M (E_wel (CEvar 0) (CEvar 4)) rho) as [dv G_dv].
  destruct (code_relation_total M (E_wel (CEvar 4) (CEvar 2)) rho) as [mc G_mc].
  destruct (code_relation_total M (E_wa (E_wel (CEvar 4) (CEvar 2)) (CEvar 5)) rho) as [rest G_rest].
  destruct (code_relation_total M (E_wa (E_wel (CEvar 0) (CEvar 4)) (E_wa (E_wel (CEvar 4) (CEvar 2)) (CEvar 5))) rho) as [source G_source].
  destruct (code_relation_total M (E_wex (CEvar 4) (E_wa (E_wel (CEvar 0) (CEvar 4)) (E_wa (E_wel (CEvar 4) (CEvar 2)) (CEvar 5)))) rho) as [exsource G_exsource].
  destruct (code_relation_total M (E_wa (E_wel (CEvar 0) (CEvar 4)) (CEvar 5)) rho) as [hasbody G_hasbody].
  destruct (code_relation_total M (E_wex (CEvar 4) (E_wa (E_wel (CEvar 0) (CEvar 4)) (CEvar 5))) rho) as [has G_has].
  destruct (code_relation_total M (E_wim (E_wex (CEvar 4) (E_wa (E_wel (CEvar 0) (CEvar 4)) (CEvar 5))) (E_wex (CEvar 4) (E_wa (E_wel (CEvar 0) (CEvar 4)) (E_wa (E_wel (CEvar 4) (CEvar 2)) (CEvar 5))))) rho) as [inner G_inner].
  exists du,ma,guard,dv,mc,rest,source,exsource,hasbody,has,inner.
  split;[exact (proj1 (ns_atom_expression M rho false (CEvar 0) (CEvar 3) t u du eq_refl eq_refl) G_du)|].
  split;[exact (proj1 (ns_atom_expression M rho false (CEvar 3) (CEvar 1) u a ma eq_refl eq_refl) G_ma)|].
  split;[exact (proj1 (quotation_binary_substitution_graph M rho SFAnd (E_wel (CEvar 0) (CEvar 3)) (E_wel (CEvar 3) (CEvar 1)) du ma guard G_du G_ma) G_guard)|].
  split;[exact (proj1 (ns_atom_expression M rho false (CEvar 0) (CEvar 4) t v dv eq_refl eq_refl) G_dv)|].
  split;[exact (proj1 (ns_atom_expression M rho false (CEvar 4) (CEvar 2) v c mc eq_refl eq_refl) G_mc)|].
  split;[exact (proj1 (quotation_binary_substitution_graph M rho SFAnd (E_wel (CEvar 4) (CEvar 2)) (CEvar 5) mc theta rest G_mc eq_refl) G_rest)|].
  split;[exact (proj1 (quotation_binary_substitution_graph M rho SFAnd (E_wel (CEvar 0) (CEvar 4)) (E_wa (E_wel (CEvar 4) (CEvar 2)) (CEvar 5)) dv rest source G_dv G_rest) G_source)|].
  split;[exact (proj1 (named_exists_expression M rho (CEvar 4) (E_wa (E_wel (CEvar 0) (CEvar 4)) (E_wa (E_wel (CEvar 4) (CEvar 2)) (CEvar 5))) v source exsource eq_refl G_source) G_exsource)|].
  split;[exact (proj1 (quotation_binary_substitution_graph M rho SFAnd (E_wel (CEvar 0) (CEvar 4)) (CEvar 5) dv theta hasbody G_dv eq_refl) G_hasbody)|].
  split;[exact (proj1 (named_exists_expression M rho (CEvar 4) (E_wa (E_wel (CEvar 0) (CEvar 4)) (CEvar 5)) v hasbody has eq_refl G_hasbody) G_has)|].
  split;[exact (proj1 (expression_implication_iff M rho (E_wex (CEvar 4) (E_wa (E_wel (CEvar 0) (CEvar 4)) (CEvar 5))) (E_wex (CEvar 4) (E_wa (E_wel (CEvar 0) (CEvar 4)) (E_wa (E_wel (CEvar 4) (CEvar 2)) (CEvar 5)))) has exsource inner G_has G_exsource) G_inner)|].
  exact (proj1 (expression_implication_iff M rho (E_wa (E_wel (CEvar 0) (CEvar 3)) (E_wel (CEvar 3) (CEvar 1))) (E_wim (E_wex (CEvar 4) (E_wa (E_wel (CEvar 0) (CEvar 4)) (CEvar 5))) (E_wex (CEvar 4) (E_wa (E_wel (CEvar 0) (CEvar 4)) (E_wa (E_wel (CEvar 4) (CEvar 2)) (CEvar 5))))) guard inner body G_guard G_inner) HB).
Qed.

Print Assumptions raw_support_clause_parts.
Print Assumptions raw_coverage_clause_parts.

