(** Exact finite site validity supplies all Load and raw Unpair execution conditions. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs Pairing
 Program230PathCode Program230Configurations Program230ParameterLoad Program230ParameterSites Program230UnpairSites
 Program230AXSymbolicGraphs Program230AXNativeSymbolic Program230AXRuntimeInterface Program230AXReadRuntime
 Program230AXPrimitiveSchedule Program230AXSiteValidity.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Lemma p230_ax_load_site_shape P e r index:
 ax_primitive_site_valid((P,e),(ALoad r,index))->
 (r<9)%nat /\r<>1 /\r<>6 /\program230_parameter_shape P r.
Proof.
 change(match nth_error p230_parameter_sites index with
 |Some site=>P=parameter_load site /\r=parameter_register site|None=>False end->
 (r<9)%nat /\r<>1 /\r<>6 /\program230_parameter_shape P r).
 destruct(nth_error p230_parameter_sites index)as[site|]eqn:HN;[|contradiction].
 intros[HP Hr];subst P r.
 assert(HI:In site p230_parameter_sites)by(eapply nth_error_In;exact HN).
 pose proof(proj1(Forall_forall _ _)p230_parameter_sites_checked site HI)as[Hbound[_[HG _]]].
 split;[lia|]. split;[lia|]. split;[lia|].
 exact(program230_parameter_node_shape _ _ _ HG).
Qed.
Theorem p230_ax_load_site_runtime M env before after start P e r index:
 ax_primitive_site_valid((P,e),(ALoad r,index))->
 program230_pc start=program230_path_value M P->program230_register start 6=zeroM M->
 p230_ax_register_graph M env before start->program230_register before 1=CEconst 0->
 p230_ax_native_step(ANLoad r)before=Some after->
 p230_ax_runtime_result M env after start(inc_path(P++[true])).
Proof.
 intro HS;destruct(p230_ax_load_site_shape P e r index HS)as[Hr[Hr1[Hr6 Hshape]]].
 exact(p230_ax_native_load_runtime M env before after start P r Hr Hr1 Hr6 Hshape).
Qed.
Lemma p230_ax_unpair_site_row P e index:
 ax_primitive_site_valid((P,e),(AUnpair 8,index))->exists n,In(P,8,n)p230_unpair_sites.
Proof.
 change(match nth_error p230_unpair_sites index with
 |Some(Q,a,n)=>P=Q /\8=a /\e=ENode n|None=>False end->exists n,In(P,8,n)p230_unpair_sites).
 destruct(nth_error p230_unpair_sites index)as[[[Q a]n]|]eqn:HN;[|contradiction].
 intros[HP[Ha He]];subst Q a;exists n;eapply nth_error_In;exact HN.
Qed.
Theorem p230_ax_unpair_site_runtime M env before after start P e index:
 ax_primitive_site_valid((P,e),(AUnpair 8,index))->
 program230_pc start=program230_path_value M P->program230_register start 6=zeroM M->
 program230_register start 7=zeroM M->p230_ax_register_graph M env before start->
 (program230_register before 8=CEvar 8 \/program230_register before 8=CEvar 9)->
 pair_graph M(env 11)(env 9)(env 8)->pair_graph M(env 4)(env 10)(env 9)->
 p230_ax_native_step ANUnpair before=Some after->p230_ax_runtime_result M env after start(inc_path P).
Proof.
 intro HS;destruct(p230_ax_unpair_site_row P e index HS)as[n Hrow].
 exact(p230_ax_native_unpair_runtime M env before after start P n Hrow).
Qed.
Print Assumptions p230_ax_load_site_shape.
Print Assumptions p230_ax_load_site_runtime.
Print Assumptions p230_ax_unpair_site_row.
Print Assumptions p230_ax_unpair_site_runtime.
