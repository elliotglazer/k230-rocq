(** Exact fixed named predicates for reflection union geometry. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 OldNamedSyntaxBridge OldFullNDSourceBridge SourceReflectionUnionOld SourceFiniteParameters SourceFiniteNameParameters SourceParameterGraphs.
From OldZFC Require Z_base Z_rel.
From Undecidability.FOL Require Import Syntax.Bounded.
From Stdlib Require Import Lia Arith.PeanoNat.
Unset Implicit Arguments.
Inductive source_reflection_geometry_predicate:=ReflectionUnion|ReflectionLimit|ReflectionNoLast|ReflectionSubsets.
Definition source_reflection_geometry_source tag:sf_form:=match tag with
 |ReflectionUnion=>isolated_formula(OldZFC.Z_base.Union0(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1))
 |ReflectionLimit=>isolated_formula(OldZFC.Z_base.Lim0(@OC.var OB.sig_empty 0))
 |ReflectionNoLast=>isolated_formula(old_reflection_no_last(@OC.var OB.sig_empty 0))
 |ReflectionSubsets=>isolated_formula(old_reflection_union_subsets(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1))end.
Definition source_reflection_geometry_arity tag:=match tag with ReflectionUnion|ReflectionSubsets=>2|_=>1 end.
Theorem source_reflection_geometry_finite_bound tag:bounded(source_reflection_geometry_arity tag)(source_reflection_geometry_source tag).
Proof.
 destruct tag;unfold source_reflection_geometry_source,source_reflection_geometry_arity;
 apply(@isolated_bounded OC.falsity_on);apply OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb;reflexivity.
Qed.
Definition source_reflection_geometry_instance M tag rho out:=code_relation M rho
 (source_parameter_expression(source_finite_parameter_names(source_reflection_geometry_arity tag))(source_reflection_geometry_source tag))out.
Theorem source_reflection_geometry_instance_total M tag rho:exists out,source_reflection_geometry_instance M tag rho out.
Proof. apply code_relation_total. Qed.
Theorem source_reflection_geometry_instance_bounded M tag rho out k:
 (forall i,(i<source_reflection_geometry_arity tag)%nat ->coding_lt M(rho i)k) ->
 source_reflection_geometry_instance M tag rho out ->source_bounded M out k.
Proof.
 intros HNames HO. apply(source_parameter_graph_bounded M(source_reflection_geometry_arity tag)(source_reflection_geometry_source tag)
  (source_reflection_geometry_finite_bound tag)(source_finite_parameter_names(source_reflection_geometry_arity tag))rho k);[|exact HO].
 intros i x HI HX. unfold source_finite_parameter_names in HX. assert(E:Nat.ltb i(source_reflection_geometry_arity tag)=true)by(now apply Nat.ltb_lt).
 rewrite E in HX. change(x=rho i)in HX. subst x. exact(HNames i HI).
Qed.
Theorem source_parameter_geometry_instance M tag names rho rho' out:
 (forall i,(i<source_reflection_geometry_arity tag)%nat ->code_relation M rho(names i)(rho' i)) ->
 code_relation M rho(source_parameter_expression names(source_reflection_geometry_source tag))out ->
 source_reflection_geometry_instance M tag rho' out.
Proof.
 intros HNames HO.
 assert(HE:forall i x,(i<source_reflection_geometry_arity tag)%nat ->
  (code_relation M rho(names i)x <->code_relation M rho'(source_finite_parameter_names(source_reflection_geometry_arity tag)i)x)).
 { intros i x HI. unfold source_finite_parameter_names. assert(E:Nat.ltb i(source_reflection_geometry_arity tag)=true)by(now apply Nat.ltb_lt).
   rewrite E. change(code_relation M rho(names i)x<->x=rho' i). split.
   - intro HX. exact(code_relation_functional M _ rho x(rho' i)HX(HNames i HI)).
   - intros ->. exact(HNames i HI). }
 exact(proj1(source_parameter_graph_ext M(source_reflection_geometry_arity tag)(source_reflection_geometry_source tag)
  (source_reflection_geometry_finite_bound tag)names(source_finite_parameter_names(source_reflection_geometry_arity tag))rho rho' HE out)HO).
Qed.
Print Assumptions source_reflection_geometry_finite_bound.
Print Assumptions source_reflection_geometry_instance_total.
Print Assumptions source_reflection_geometry_instance_bounded.
Print Assumptions source_parameter_geometry_instance.
