(** Finite source role substitution preserves the exact numerical compiler graph. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceFiniteParameters SourceFiniteNameParameters
 SourceFiniteParameterComposition SourceFiniteParameterNamedBinder SourceParameterGraphs.
From Undecidability.FOL Require Import Syntax.Bounded.
Unset Implicit Arguments.
Theorem source_local_parameter_reindex M bound(phi:sf_form)names sigma rho target out:
 bounded bound phi ->(forall i,(i<bound)%nat ->code_relation M rho(names(sf_index(sigma i)))(target i)) ->
 code_relation M target(source_parameter_expression(source_finite_parameter_names bound)phi)out ->
 code_relation M rho(source_parameter_expression names(phi[sigma]))out.
Proof.
 intros HB HNames HOut. rewrite source_parameter_substitution.
 assert(HE:forall i x,(i<bound)%nat ->
  (code_relation M rho(names(sf_index(sigma i)))x <->
   code_relation M target(source_finite_parameter_names bound i)x)).
 { intros i x HI. pose proof(HNames i HI)as HA.
   pose proof(finite_parameter_name_graph M bound target i HI)as HB'. split;intro HX.
   - rewrite(code_relation_functional M _ rho x(target i)HX HA). exact HB'.
   - rewrite(code_relation_functional M _ target x(target i)HX HB'). exact HA. }
 exact(proj2(source_parameter_graph_ext M bound phi HB
  (fun i=>names(sf_index(sigma i)))(source_finite_parameter_names bound)rho target HE out)HOut).
Qed.
Print Assumptions source_local_parameter_reindex.
