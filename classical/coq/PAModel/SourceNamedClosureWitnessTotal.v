(** Construct the actual named witness codes and transport their already
    proved canonical closure statement. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourceRepresentativeRenaming SourceNamedQuantifierRules SourceEnvironmentCarrierClosure
 SourceNamedClosureExistence SourcePropositionalTemplates SourceZFRProvability.
Unset Implicit Arguments.
Theorem source_zfr_named_closure_witness_total M rep canonical r named:
 source_bounded M rep(code_numeral M 2)->
 source_environment_carrier_closure_statement M rep canonical->source_zfr_provable M canonical->
 ~coding_lt M r(code_numeral M 3)->source_representative_renaming M r rep named->
 exists member body ex out,sf_relation M SFMember r(code_numeral M 2)member/\sf_relation M SFAnd member named body/\
 source_named_quantifier M false r body ex/\
 code_relation M(named_closure_values M ex)(source_prop_expression NCE_template)out/\source_zfr_provable M out.
Proof.
 intros BRep HCanonical PCanonical HR HNamed.
 destruct(sf_relation_total M SFMember r(code_numeral M 2))as(member&HMember).
 destruct(sf_relation_total M SFAnd member named)as(body&HBody).
 destruct(source_named_quantifier_total M false r body)as(ex&HEx).
 destruct(code_relation_total M(source_prop_expression NCE_template)(named_closure_values M ex))as(out&HOut).
 exists member,body,ex,out. refine(conj HMember(conj HBody(conj HEx(conj HOut _)))).
 exact(source_zfr_named_closure_existence M rep canonical r named member body ex out BRep HCanonical PCanonical HR HNamed HMember HBody HEx HOut).
Qed.
Print Assumptions source_zfr_named_closure_witness_total.
