(** Literal decomposition of the actual finite cofinal extension proof.
    No ordinal or hierarchy inference is supplied as an assumed proof family. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SchemaConstructorBounds NumericalInstantiation
 SourceCofinalLevelExtension SourceCofinalLevelExtensionOld SourceCofinalGeometry SourceCommonLevelBase
 SourceFiniteParameters SourceFiniteNameParameters SourceParameterGraphs SourcePropositionalRebase
 SourceOrdinalParameterCalibration SourceHierarchyCalibration SourceSubsetParameterCalibration
 SourceOrdinalPredicate SourceHierarchySyntax SourceRawSubset OldNamedSyntaxBridge SourceZFRProvability.
From OldZFC Require Z_base Z_L.
From Stdlib Require Import Lia Arith.PeanoNat.
Unset Implicit Arguments.
Lemma source_cofinal_parameter_two_binders M names rho i x:
 code_relation M rho(names i)x ->code_relation M rho(source_parameter_up(source_parameter_up names)(S(S i)))(succM M(succM M x)).
Proof.
 intro H. change(code_relation M rho(CEadd(CEadd(names i)(CEconst 1))(CEconst 1))(succM M(succM M x))).
 exists(succM M x),(code_numeral M 1). split.
 - exists x,(code_numeral M 1). split;[exact H|]. split;[reflexivity|]. apply Arithmetic.succ_as_add.
 - split;[reflexivity|]. apply Arithmetic.succ_as_add.
Qed.
Definition source_cofinal_extension_shell M K Lb d X y ordinals cover oldmember oldlevel newmember
 exD bodyD bodyY kmem ordinal level pair left subset member right tail4 tail3 tail2 tail1 law :=
 source_cofinal_ordinals M K ordinals /\source_cofinal_cover M K Lb cover /\
 sf_relation M SFMember d K oldmember /\source_LL_instance M d X oldlevel /\sf_relation M SFMember y Lb newmember /\
 sf_relation M SFMember(code_numeral M 1)(succM M(succM M K))kmem /\
 numerical_instantiation M(source_ordinal_predicate_code M)(code_numeral M 1)ordinal /\
 source_LL_instance M(code_numeral M 1)(zeroM M)level /\
 sf_relation M SFAnd kmem ordinal pair /\sf_relation M SFAnd pair level left /\
 source_raw_subset_graph M(succM M(succM M X))(zeroM M)subset /\
 sf_relation M SFMember(succM M(succM M y))(zeroM M)member /\
 sf_relation M SFAnd subset member right /\sf_relation M SFAnd left right bodyY /\
 sf_relation M SFEx bodyY(zeroM M)bodyD /\sf_relation M SFEx bodyD(zeroM M)exD /\
 sf_relation M SFImpl newmember exD tail4 /\sf_relation M SFImpl oldlevel tail4 tail3 /\
 sf_relation M SFImpl oldmember tail3 tail2 /\sf_relation M SFImpl cover tail2 tail1 /\
 sf_relation M SFImpl ordinals tail1 law.
Theorem source_zfr_cofinal_extension_shell M K Lb d X y:
 exists ordinals cover oldmember oldlevel newmember exD bodyD bodyY kmem ordinal level pair left subset member right tail4 tail3 tail2 tail1 law,
 source_cofinal_extension_shell M K Lb d X y ordinals cover oldmember oldlevel newmember
 exD bodyD bodyY kmem ordinal level pair left subset member right tail4 tail3 tail2 tail1 law /\source_zfr_provable M law.
Proof.
 set(rho:=fun i:nat=>match i with 0=>K|1=>Lb|2=>d|3=>X|_=>y end).
 set(names:=source_finite_parameter_names 5).
 set(deep:=source_parameter_up(source_parameter_up names)).
 destruct(code_relation_total M source_cofinal_extension_expression rho)as(law&HLaw).
 pose proof(source_zfr_cofinal_level_extension M rho law HLaw)as PLaw.
 change(code_relation M rho(E_sf SFImpl(source_parameter_expression names source_cofinal_ordinals_predicate)
 (E_sf SFImpl(source_parameter_expression names source_cofinal_cover_predicate)
 (E_sf SFImpl(E_sf SFMember(names 2)(names 0))
 (E_sf SFImpl(source_parameter_expression names(isolated_formula(OldZFC.Z_L.LL(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 3))))
 (E_sf SFImpl(E_sf SFMember(names 4)(names 1))
 (E_sf SFEx(E_sf SFEx(E_sf SFAnd
 (E_sf SFAnd(E_sf SFAnd(E_sf SFMember(deep 1)(deep 2))
 (source_parameter_expression deep source_common_empty_ordinal))
 (source_parameter_expression deep source_common_empty_level))
 (E_sf SFAnd(source_parameter_expression deep(isolated_formula(OldZFC.Z_base.Sub0(@OC.var OB.sig_empty 5)(@OC.var OB.sig_empty 0))))
 (E_sf SFMember(deep 6)(deep 0))))(CEconst 0))(CEconst 0)))))))law)in HLaw.
 destruct(schema_expression_split M rho _ _ _ law HLaw)as(ordinals&tail1&HOrdinals&HTail1&HImp1).
 destruct(schema_expression_split M rho _ _ _ tail1 HTail1)as(cover&tail2&HCover&HTail2&HImp2).
 destruct(schema_expression_split M rho _ _ _ tail2 HTail2)as(oldmember&tail3&HOldMember&HTail3&HImp3).
 destruct(schema_expression_split M rho _ _ _ tail3 HTail3)as(oldlevel&tail4&HOldLevel&HTail4&HImp4).
 destruct(schema_expression_split M rho _ _ _ tail4 HTail4)as(newmember&exD&HNewMember&HExD&HImp5).
 destruct(schema_expression_split M rho _ _ _ exD HExD)as(bodyD&zero1&HBodyD&HZ1&HEx1).
 change(zero1=zeroM M)in HZ1. subst zero1.
 destruct(schema_expression_split M rho _ _ _ bodyD HBodyD)as(bodyY&zero2&HBodyY&HZ2&HEx2).
 change(zero2=zeroM M)in HZ2. subst zero2.
 destruct(schema_expression_split M rho _ _ _ bodyY HBodyY)as(left&right&HLeft&HRight&HBody).
 destruct(schema_expression_split M rho _ _ _ left HLeft)as(pair&level&HPair&HLevel&HLeftAnd).
 destruct(schema_expression_split M rho _ _ _ pair HPair)as(kmem&ordinal&HKMem&HOrdinal&HPairAnd).
 destruct(schema_expression_split M rho _ _ _ right HRight)as(subset&member&HSubset&HMember&HRightAnd).
 assert(HNames:forall i,(i<5)%nat ->code_relation M rho(names i)(rho i)).
 { intros i HI. unfold names,source_finite_parameter_names. rewrite(proj2(Nat.ltb_lt i 5)HI). reflexivity. }
 assert(HDeep0:code_relation M rho(deep 0)(zeroM M))by reflexivity.
 assert(HDeep1:code_relation M rho(deep 1)(code_numeral M 1)).
 { change(code_relation M rho(CEadd(CEconst 0)(CEconst 1))(code_numeral M 1)).
   exists(zeroM M),(code_numeral M 1). split;[reflexivity|]. split;[reflexivity|]. symmetry. apply coding_add_zero. }
 assert(HDeep2:code_relation M rho(deep 2)(succM M(succM M K))).
 { exact(source_cofinal_parameter_two_binders M names rho 0 K(HNames 0 ltac:(lia))). }
 assert(HDeep5:code_relation M rho(deep 5)(succM M(succM M X))).
 { exact(source_cofinal_parameter_two_binders M names rho 3 X(HNames 3 ltac:(lia))). }
 assert(HDeep6:code_relation M rho(deep 6)(succM M(succM M y))).
 { exact(source_cofinal_parameter_two_binders M names rho 4 y(HNames 4 ltac:(lia))). }
 exists ordinals,cover,oldmember,oldlevel,newmember,exD,bodyD,bodyY,kmem,ordinal,level,pair,left,subset,member,right,
 tail4,tail3,tail2,tail1,law. split;[|exact PLaw]. unfold source_cofinal_extension_shell.
 split.
 - apply(proj2(source_parameter_graph_ext M 1 source_cofinal_ordinals_predicate source_cofinal_ordinals_finite_bound
   (source_finite_parameter_names 1)names(fun _=>K)rho ltac:(intros[|i]z HI;try lia;reflexivity)ordinals)). exact HOrdinals.
 - split.
   + apply(proj2(source_parameter_graph_ext M 2 source_cofinal_cover_predicate source_cofinal_cover_finite_bound
     (source_finite_parameter_names 2)names(fun i=>match i with 0=>K|_=>Lb end)rho
     ltac:(intros[|[|i]]z HI;try lia;reflexivity)cover)). exact HCover.
   + split.
     * exact(proj1(schema_expression_graph M rho SFMember(names 2)(names 0)d K oldmember(HNames 2 ltac:(lia))(HNames 0 ltac:(lia)))HOldMember).
     * split.
       -- exact(source_parameter_LL_instance M names rho 2 3 d X oldlevel(HNames 2 ltac:(lia))(HNames 3 ltac:(lia))HOldLevel).
       -- split.
          ++ exact(proj1(schema_expression_graph M rho SFMember(names 4)(names 1)y Lb newmember(HNames 4 ltac:(lia))(HNames 1 ltac:(lia)))HNewMember).
          ++ split.
             ** exact(proj1(schema_expression_graph M rho SFMember(deep 1)(deep 2)(code_numeral M 1)(succM M(succM M K))kmem HDeep1 HDeep2)HKMem).
             ** split.
                --- exact(source_parameter_ordinal_instance M deep rho 1(code_numeral M 1)ordinal HDeep1 HOrdinal).
                --- split.
                    +++ exact(source_parameter_LL_instance M deep rho 1 0(code_numeral M 1)(zeroM M)level HDeep1 HDeep0 HLevel).
                    +++ split;[exact HPairAnd|]. split;[exact HLeftAnd|]. split.
                        *** exact(source_parameter_raw_subset M deep rho 5 0(succM M(succM M X))(zeroM M)subset HDeep5 HDeep0 HSubset).
                        *** split.
                            ---- exact(proj1(schema_expression_graph M rho SFMember(deep 6)(deep 0)(succM M(succM M y))(zeroM M)member HDeep6 HDeep0)HMember).
                            ---- repeat first[assumption|split].
Qed.
Print Assumptions source_zfr_cofinal_extension_shell.
