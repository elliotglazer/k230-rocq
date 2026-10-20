(** Compile the comparison and irreflexivity deductions into a real source proof. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourceNumFDistinctPrograms SourcePropositionalTemplates SourceWitnessProofComposition SourceZFRProvability.
Unset Implicit Arguments.
Ltac nd_graph :=lazymatch goal with
 | |-code_relation ?M ?rho(source_prop_expression(SPTSlot ?idx))?out=>reflexivity
 | |-code_relation ?M ?rho(source_prop_expression SPTFalse)?out=>reflexivity
 | |-code_relation ?M ?rho(source_prop_expression(SPTImpl ?A ?B))?out=>
  match goal with H:sf_relation M SFImpl ?a ?b out|-_=>apply(source_prop_template_join M rho SFImpl A B a b out);[nd_graph|nd_graph|exact H]end
 end.
Theorem source_zfr_numf_distinct_composition M (reverse:bool) p qs member equal neg inner result mi ml fact bound:
 source_bounded M p bound ->source_bounded M qs bound ->source_bounded M member bound ->source_bounded M equal bound ->
 sf_relation M SFImpl equal(zeroM M)neg ->sf_relation M SFImpl qs neg inner ->sf_relation M SFImpl p inner result ->
 sf_relation M SFImpl(if reverse then p else qs)member mi ->
 sf_relation M SFImpl(if reverse then qs else p)mi ml ->sf_relation M SFImpl member neg fact ->
 source_zfr_provable M ml ->source_zfr_provable M fact ->source_zfr_provable M result.
Proof.
 intros BP BQ BM BE HN HI HO HMI HML HF PM PF.
 set(env:=fun idx:nat=>match idx with 0=>p|1=>qs|2=>member|_=>equal end).
 apply(source_zfr_prop_two M(nd_member reverse)nd_fact nd_law(source_numf_distinct_program reverse)env bound ml fact result).
 - intros[|[|[|idx]]];cbn[env];assumption.
 - destruct reverse;unfold nd_member;nd_graph.
 - unfold nd_fact. nd_graph.
 - unfold nd_law. nd_graph.
 - exact PM.
 - exact PF.
Qed.
Print Assumptions source_zfr_numf_distinct_composition.
