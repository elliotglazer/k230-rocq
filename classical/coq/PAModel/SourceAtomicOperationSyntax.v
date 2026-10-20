(** Literal four-role syntax of atomic representation operations. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes OldNamedSyntaxBridge OldFullNDSourceBridge
 SourceFiniteParameters SourceFiniteParameterComposition SourceFiniteNameParameters SourceParameterGraphs SourceParameterTransport NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution RenamingSubstitution.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF.
From OldZFC Require Z_cl Z_rel.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Definition source_atomic_operation_predicate(member:bool):sf_form:=isolated_formula
 (OldZFC.Z_cl.Op(if member then 6 else 7)(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 3)).
Definition source_atomic_operation_environment{A}(a b c r:A)i:=match i with 0=>a|1=>b|2=>c|_=>r end.
Definition source_atomic_operation M member a b c r out:=code_relation M(source_atomic_operation_environment a b c r)
 (source_parameter_expression(source_finite_parameter_names 4)(source_atomic_operation_predicate member))out.
Lemma source_atomic_operation_finite_bound member:
 Undecidability.FOL.Syntax.Bounded.bounded 4(source_atomic_operation_predicate member).
Proof.
 unfold source_atomic_operation_predicate. apply(@isolated_bounded OC.falsity_on 4),OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb.
 destruct member;reflexivity.
Qed.
Lemma isolated_atomic_operation_at(member:bool) a b c r:
 isolated_formula(OldZFC.Z_cl.Op(if member then 6 else 7)a b c r)=
 C.subst_form(C.scons(isolated_term a)(C.scons(isolated_term b)(C.scons(isolated_term c)(C.scons(isolated_term r)C.var))))
 (source_atomic_operation_predicate member).
Proof.
 pose proof(isolated_formula_subst(OldZFC.Z_cl.Op(if member then 6 else 7)(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 3))
  (OC.scons a(OC.scons b(OC.scons c(OC.scons r OC.var))))
  (C.scons(isolated_term a)(C.scons(isolated_term b)(C.scons(isolated_term c)(C.scons(isolated_term r)C.var))))
  ltac:(intros[|[|[|[|i]]]];reflexivity))as E.
 rewrite OldZFC.Z_cl.Op_subst in E. exact E.
Qed.
Theorem source_parameter_atomic_operation_instance M(member:bool)names rho a b c r av bv cv rv out:
 code_relation M rho(names a)av->code_relation M rho(names b)bv->code_relation M rho(names c)cv->code_relation M rho(names r)rv->
 code_relation M rho(source_parameter_expression names(isolated_formula(OldZFC.Z_cl.Op(if member then 6 else 7)
  (@OC.var OB.sig_empty a)(@OC.var OB.sig_empty b)(@OC.var OB.sig_empty c)(@OC.var OB.sig_empty r))))out->
 source_atomic_operation M member av bv cv rv out.
Proof.
 intros HA HB HC HR HG. rewrite isolated_atomic_operation_at,source_parameter_substitution in HG.
 set(sg:=C.scons(C.var a)(C.scons(C.var b)(C.scons(C.var c)(C.scons(C.var r)C.var)))).
 assert(HNames:forall i v,(i<4)%nat->
  (code_relation M rho(names(sf_index(sg i)))v<->code_relation M(source_atomic_operation_environment av bv cv rv)(source_finite_parameter_names 4 i)v)).
 { intros[|[|[|[|i]]]]v HI;try lia.
   - change(code_relation M rho(names a)v<->v=av). split;[intro H;exact(code_relation_functional M(names a)rho v av H HA)|intros->;exact HA].
   - change(code_relation M rho(names b)v<->v=bv). split;[intro H;exact(code_relation_functional M(names b)rho v bv H HB)|intros->;exact HB].
   - change(code_relation M rho(names c)v<->v=cv). split;[intro H;exact(code_relation_functional M(names c)rho v cv H HC)|intros->;exact HC].
   - change(code_relation M rho(names r)v<->v=rv). split;[intro H;exact(code_relation_functional M(names r)rho v rv H HR)|intros->;exact HR]. }
 exact(proj1(source_parameter_graph_ext M 4(source_atomic_operation_predicate member)(source_atomic_operation_finite_bound member)
  (fun i=>names(sf_index(sg i)))(source_finite_parameter_names 4)rho(source_atomic_operation_environment av bv cv rv)HNames out)HG).
Qed.
Theorem source_atomic_operation_total M member a b c r:exists out,source_atomic_operation M member a b c r out.
Proof. apply code_relation_total. Qed.
Theorem source_atomic_operation_renaming M member a b c r out a' b' c' r' other rb rc rn delta:
 source_atomic_operation M member a b c r out->source_atomic_operation M member a' b' c' r' other->
 renaming_lookup M rb rc rn delta a a'->renaming_lookup M rb rc rn delta b b'->
 renaming_lookup M rb rc rn delta c c'->renaming_lookup M rb rc rn delta r r'->
 numerical_renaming M out rb rc rn delta other.
Proof.
 intros HO HN HA HB HC HR. apply(proj2(numerical_renaming_substitution M out rb rc rn delta other)).
 apply(source_parameter_transport M 4(source_atomic_operation_predicate member)(source_atomic_operation_finite_bound member)
  (source_finite_parameter_names 4)(source_finite_parameter_names 4)(source_atomic_operation_environment a b c r)
  (source_atomic_operation_environment a' b' c' r')rb rc rn(addM M rn delta)out other);[|exact HO|exact HN].
 intros[|[|[|[|i]]]]x y HI HX HY;try lia.
 - change(x=a)in HX. change(y=a')in HY. subst x y. exact(proj1(renaming_substitution_lookup M rb rc rn delta a a')HA).
 - change(x=b)in HX. change(y=b')in HY. subst x y. exact(proj1(renaming_substitution_lookup M rb rc rn delta b b')HB).
 - change(x=c)in HX. change(y=c')in HY. subst x y. exact(proj1(renaming_substitution_lookup M rb rc rn delta c c')HC).
 - change(x=r)in HX. change(y=r')in HY. subst x y. exact(proj1(renaming_substitution_lookup M rb rc rn delta r r')HR).
Qed.
Print Assumptions source_parameter_atomic_operation_instance.
Print Assumptions source_atomic_operation_total.
Print Assumptions source_atomic_operation_renaming.
