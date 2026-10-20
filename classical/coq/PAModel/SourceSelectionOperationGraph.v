(** Exact graph of the fixed Op5 selection law. The right side uses the
    same literal SC predicate proved correct for arbitrary source matrices. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceLocalDefinabilityFixed
 SourceSelectionSCBinder SourceFiniteParameters SourceFiniteNameParameters SourceFiniteParameterComposition
 SourceParameterGraphs SourceFiniteParameterProofs SourceEnvironmentCarrierClosure SourceIffGraphs
 OldNamedSyntaxBridge OldFullNDSourceBridge.
From OldZFC Require Z_cl Z_rel.
From Undecidability.FOL Require Import Syntax.Facts Syntax.Bounded Sets.minZF.
From Stdlib Require Import Lia Arith.PeanoNat.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition source_local_operation5:sf_form:=isolated_formula(OldZFC.Z_cl.Op 5
 (@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 3)).
Definition source_local_operation5_expression:=source_parameter_expression(source_finite_parameter_names 4)source_local_operation5.
Definition local_operation5_names {A}(rep old carrier selected:A)i:=match i with 0=>rep|1=>old|2=>carrier|_=>selected end.
Definition local_selection_law_names {A}(rep old carrier selected tested:A)i:=match i with
 |0=>rep|1=>old|2=>carrier|3=>selected|_=>tested end.
Definition local_selection_SC_sigma i:sf_term:=match i with 0=>$0|1=>$1|2=>$4|_=>$(i)end.
Lemma source_local_selection_law_shape:source_local_selection_operation_law=
 source_local_operation5 →($4 ∈' $3 ↔($4 ∈' $2 ∧source_local_SC[local_selection_SC_sigma])).
Proof. reflexivity. Qed.
Lemma source_local_operation5_bound:bounded 4 source_local_operation5.
Proof.
 unfold source_local_operation5. apply(@isolated_bounded OC.falsity_on 4),OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity.
Qed.
Theorem source_local_selection_operation_graph M rep old carrier selected tested operation inY inA sc pair profile law:
 code_relation M(local_operation5_names rep old carrier selected)source_local_operation5_expression operation ->
 sf_relation M SFMember tested selected inY ->sf_relation M SFMember tested carrier inA ->
 code_relation M(local_SC_names rep old tested)source_local_SC_expression sc ->sf_relation M SFAnd inA sc pair ->
 source_iff_graph M inY pair profile ->sf_relation M SFImpl operation profile law ->
 code_relation M(local_selection_law_names rep old carrier selected tested)source_local_selection_operation_expression law.
Proof.
 intros HOp HY HA HSC HPair HProfile HLaw.
 set(rho:=local_selection_law_names rep old carrier selected tested).
 assert(GOp:code_relation M rho(source_parameter_expression(source_finite_parameter_names 5)source_local_operation5)operation).
 { apply(proj2(source_parameter_graph_ext M 4 source_local_operation5 source_local_operation5_bound
    (source_finite_parameter_names 5)(source_finite_parameter_names 4)rho(local_operation5_names rep old carrier selected)
    ltac:(intros[|[|[|[|i]]]]v HI;try lia;reflexivity)operation)). exact HOp. }
 assert(BSC:bounded 3 source_local_SC)by(constructor;exact source_local_SC_body_bound).
 assert(GSC:code_relation M rho(source_parameter_expression(source_finite_parameter_names 5)
  (source_local_SC[local_selection_SC_sigma]))sc).
 { rewrite source_parameter_substitution.
   apply(proj2(source_parameter_graph_ext M 3 source_local_SC
    BSC
    (fun i=>source_finite_parameter_names 5(sf_index(local_selection_SC_sigma i)))
    (source_finite_parameter_names 3)rho(local_SC_names rep old tested)
    ltac:(intros[|[|[|i]]]v HI;try lia;reflexivity)sc)). exact HSC. }
 assert(GY:code_relation M rho(E_sf SFMember(CEvar 4)(CEvar 3))inY).
 { eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HY]. }
 assert(GA:code_relation M rho(E_sf SFMember(CEvar 4)(CEvar 2))inA).
 { eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HA]. }
 unfold source_local_selection_operation_expression. rewrite source_local_selection_law_shape.
 cbn[source_parameter_expression].
 eapply environment_carrier_code_join;[exact GOp| |exact HLaw].
 destruct(source_iff_parts M inY pair profile HProfile)as(lr&rl&HLR&HRL&HAnd).
 eapply environment_carrier_code_join;[| |exact HAnd].
 - eapply environment_carrier_code_join;[exact GY| |exact HLR].
   eapply environment_carrier_code_join;[exact GA|exact GSC|exact HPair].
 - eapply environment_carrier_code_join;[|exact GY|exact HRL].
   eapply environment_carrier_code_join;[exact GA|exact GSC|exact HPair].
Qed.
Print Assumptions source_local_selection_law_shape.
Print Assumptions source_local_selection_operation_graph.
