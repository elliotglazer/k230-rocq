(** Literal hierarchy uniqueness and witness-above laws, including their
    actual ZFR proofs at arbitrary internally coded variable names. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes NumericalInstantiation
  SourceHierarchySyntax SourceHierarchyCalibration SourceHierarchyWitnessFixed SourceHierarchyWitnessOld
  SourceFiniteParameters SourceFiniteNameParameters SourceFiniteParameterComposition SourceUnaryParameters
  SourceOrdinalPredicate SourceOrdinalParameterCalibration SourceOrdinalMemberShell
  SourceLFixed SourceZFRProvability SourcePropositionalRebase OldNamedSyntaxBridge OldFullNDSourceBridge SubstitutionSource.
From OldZFC Require Z_L.
Unset Implicit Arguments.
Local Opaque source_LL_predicate source_ordinal_predicate source_L_domain.

Definition source_hierarchy_unique_shell M d u v od ld le equal t1 t2 law :=
  numerical_instantiation M(source_ordinal_predicate_code M) d od /\
  source_LL_instance M d u ld /\source_LL_instance M d v le /\sf_relation M SFEqual u v equal /\
  sf_relation M SFImpl le equal t2 /\sf_relation M SFImpl ld t2 t1 /\sf_relation M SFImpl od t1 law.

Theorem source_zfr_hierarchy_unique_shell M d u v :exists od ld le equal t1 t2 law,
  source_hierarchy_unique_shell M d u v od ld le equal t1 t2 law /\source_zfr_provable M law.
Proof.
  set(rho:=fun i=>match i with 0=>d|1=>u|_=>v end).
  set(names:=source_finite_parameter_names 4).
  destruct(code_relation_total M source_hierarchy_unique_expression rho) as(law&HG).
  pose proof(source_zfr_hierarchy_unique M rho law HG) as PLaw.
  unfold source_hierarchy_unique_expression,source_hierarchy_unique_law,old_hierarchy_unique_law in HG.
  change(code_relation M rho(E_sf SFImpl
    (source_parameter_expression names(isolated_formula(OldZFC.Z_base.Ord0(@OC.var OB.sig_empty 0))))
    (E_sf SFImpl(source_parameter_expression names(isolated_formula(OldZFC.Z_L.LL
      (@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1))))
      (E_sf SFImpl(source_parameter_expression names(isolated_formula(OldZFC.Z_L.LL
        (@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 2))))(E_sf SFEqual(CEvar 1)(CEvar 2))))) law) in HG.
  destruct(schema_expression_split M rho _ _ _ law HG) as(od&t1&HOD&HT1&H0).
  destruct(schema_expression_split M rho _ _ _ t1 HT1) as(ld&t2&HLD&HT2&H1).
  destruct(schema_expression_split M rho _ _ _ t2 HT2) as(le&equal&HLE&HE&H2).
  assert(N0:code_relation M rho(names 0)d) by reflexivity.
  assert(N1:code_relation M rho(names 1)u) by reflexivity.
  assert(N2:code_relation M rho(names 2)v) by reflexivity.
  exists od,ld,le,equal,t1,t2,law. split;[|exact PLaw].
  split;[exact(source_parameter_ordinal_instance M names rho 0 d od N0 HOD)|].
  split;[exact(source_parameter_LL_instance M names rho 0 1 d u ld N0 N1 HLD)|].
  split;[exact(source_parameter_LL_instance M names rho 0 2 d v le N0 N2 HLE)|].
  repeat split;assumption.
Qed.

Lemma isolated_InL_at t :isolated_formula(OldZFC.Z_L.InL t)=
  C.subst_form(C.scons(isolated_term t)C.var) source_L_domain.
Proof. exact(isolated_old_formula_instantiate OldZFC.Z_L.Lform t). Qed.

Theorem source_parameter_L_instance M names rho i name out :
  code_relation M rho(names i) name ->
  code_relation M rho(source_parameter_expression names
    (isolated_formula(OldZFC.Z_L.InL(@OC.var OB.sig_empty i)))) out ->
  numerical_instantiation M(source_L_domain_code M) name out.
Proof.
  intros HName HG. rewrite isolated_InL_at,source_parameter_substitution in HG.
  exact(source_unary_parameter_instantiation M source_L_domain
    (fun j=>names(sf_index((C.scons(isolated_term(@OC.var OB.sig_empty i)) C.var)j)))
    rho name out source_L_domain_bounded HName HG).
Qed.

Definition source_hierarchy_above_shell M y g ly og exD bodyD bodyY od subset pair level inner member tail law :=
  numerical_instantiation M(source_L_domain_code M)y ly /\
  numerical_instantiation M(source_ordinal_predicate_code M)g og /\
  numerical_instantiation M(source_ordinal_predicate_code M)(code_numeral M 1)od /\
  source_LL_instance M(code_numeral M 1)(zeroM M)level /\
  sf_relation M SFMember(succM M(succM M y))(zeroM M)member /\
  sf_relation M SFAnd od subset pair /\sf_relation M SFAnd pair level inner /\
  sf_relation M SFAnd inner member bodyY /\sf_relation M SFEx bodyY(zeroM M)bodyD /\
  sf_relation M SFEx bodyD(zeroM M)exD /\sf_relation M SFImpl og exD tail /\
  sf_relation M SFImpl ly tail law.

Theorem source_zfr_hierarchy_above_shell M y g :
  exists ly og exD bodyD bodyY od subset pair level inner member tail law,
    source_hierarchy_above_shell M y g ly og exD bodyD bodyY od subset pair level inner member tail law /\
    source_zfr_provable M law.
Proof.
  set(rho:=fun i=>match i with 0=>y|_=>g end).
  set(names:=source_finite_parameter_names 4).
  set(up1:=source_parameter_up names).
  set(up2:=source_parameter_up up1).
  destruct(code_relation_total M source_hierarchy_above_expression rho) as(law&HG).
  pose proof(source_zfr_hierarchy_above M rho law HG) as PLaw.
  unfold source_hierarchy_above_expression,source_hierarchy_above_law,old_hierarchy_above_law in HG.
  change(code_relation M rho(E_sf SFImpl
    (source_parameter_expression names(isolated_formula(OldZFC.Z_L.InL(@OC.var OB.sig_empty 0))))
    (E_sf SFImpl(source_parameter_expression names(isolated_formula(OldZFC.Z_base.Ord0(@OC.var OB.sig_empty 1))))
      (E_sf SFEx(E_sf SFEx(E_sf SFAnd
        (E_sf SFAnd(E_sf SFAnd
          (source_parameter_expression up2(isolated_formula(OldZFC.Z_base.Ord0(@OC.var OB.sig_empty 1))))
          (source_parameter_expression up2(isolated_formula(OldZFC.Z_base.Sub0(@OC.var OB.sig_empty 3)(@OC.var OB.sig_empty 1)))))
          (source_parameter_expression up2(isolated_formula(OldZFC.Z_L.LL(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 0)))))
        (E_sf SFMember(up2 2)(up2 0)))(CEconst 0))(CEconst 0)))) law) in HG.
  destruct(schema_expression_split M rho _ _ _ law HG) as(ly&tail&HLY&HTail&H0).
  destruct(schema_expression_split M rho _ _ _ tail HTail) as(og&exD&HOG&HExD&H1).
  destruct(schema_expression_split M rho SFEx _ (CEconst 0) exD HExD) as(bodyD&unused&HBodyD&HU&H2).
  change(unused=zeroM M) in HU. subst unused.
  destruct(schema_expression_split M rho SFEx _ (CEconst 0) bodyD HBodyD) as(bodyY&unused&HBodyY&HU&H3).
  change(unused=zeroM M) in HU. subst unused.
  destruct(schema_expression_split M rho _ _ _ bodyY HBodyY) as(inner&member&HInner&HMember&H4).
  destruct(schema_expression_split M rho _ _ _ inner HInner) as(pair&level&HPair&HLevel&H5).
  destruct(schema_expression_split M rho _ _ _ pair HPair) as(od&subset&HOD&HSubset&H6).
  assert(N0:code_relation M rho(names 0)y) by reflexivity.
  assert(N1:code_relation M rho(names 1)g) by reflexivity.
  assert(U0:code_relation M rho(up2 0)(zeroM M)) by reflexivity.
  assert(U1:code_relation M rho(up2 1)(code_numeral M 1)).
  { exact(source_code_successor_graph M rho(CEconst 0)(zeroM M) eq_refl). }
  assert(U2:code_relation M rho(up2 2)(succM M(succM M y))).
  { apply(source_code_successor_graph M rho(up1 1)(succM M y)).
    exact(source_code_successor_graph M rho(names 0)y N0). }
  exists ly,og,exD,bodyD,bodyY,od,subset,pair,level,inner,member,tail,law. split;[|exact PLaw].
  split;[exact(source_parameter_L_instance M names rho 0 y ly N0 HLY)|].
  split;[exact(source_parameter_ordinal_instance M names rho 1 g og N1 HOG)|].
  split;[exact(source_parameter_ordinal_instance M up2 rho 1(code_numeral M 1)od U1 HOD)|].
  split;[exact(source_parameter_LL_instance M up2 rho 1 0(code_numeral M 1)(zeroM M)level U1 U0 HLevel)|].
  split;[exact(proj1(substitution_source_constructor_graph M rho SFMember(up2 2)(up2 0)
    (succM M(succM M y))(zeroM M)member U2 U0)HMember)|].
  repeat split;assumption.
Qed.

Print Assumptions source_zfr_hierarchy_unique_shell.
Print Assumptions source_parameter_L_instance.
Print Assumptions source_zfr_hierarchy_above_shell.
