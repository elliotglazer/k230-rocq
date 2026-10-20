(** Literal current-graph calibration of the fixed fresh predecessor law. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes OldNamedSyntaxBridge OldFullNDSourceBridge SourceFiniteParameters SourceFiniteNameParameters
 SourceRecursionPrimitiveRelations SourceRecursionStructureGraphs SourceRecursionParameterCalibration SourceRecursionSuccessorCalibration
 SourceRecursionSetOperations SourceRecursionFreshPredecessorFixed SourceFiniteTelescope SourcePropositionalRebase SchemaConstructorBounds SourceZFRProvability.
From OldZF Require Std_setbase Std_setrec Std_setinf.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition source_rec_env9 {A:Type}(a b c d e f g h j:A)i:=match i with 0=>a|1=>b|2=>c|3=>d|4=>e|5=>f|6=>g|7=>h|_=>j end.
Ltac rec_pack_telescope:=first[reflexivity|match goal with
 |H:sf_relation ?M SFImpl ?head ?inner ?out |-source_finite_telescope ?M (?head::?A) ?target ?out =>
 exists inner;split;[rec_pack_telescope|exact H]end].
Theorem source_rec_fresh_predecessor_shell M N z next f v q g u nextu law:
 code_relation M(source_rec_env9 N z next f v q g u nextu)source_rec_fresh_predecessor_expression law ->
 exists inj mz sz appf adj mu su equal appg,
 source_rec_injectivity M N inj /\sf_relation M SFMember z N mz /\source_rec_successor M z next sz /\source_rec_app M f z v appf /\
 source_rec_adjoin M f q g adj /\sf_relation M SFMember u N mu /\source_rec_successor M u nextu su /\sf_relation M SFEqual nextu next equal /\
 source_rec_app M g u v appg /\source_finite_telescope M[inj;mz;sz;appf;adj;mu;su;equal]appg law.
Proof.
 intro HG. set(rho:=source_rec_env9 N z next f v q g u nextu). set(names:=source_finite_parameter_names 9).
 set(INJ:=source_parameter_expression names(isolated_formula(OldZF.Std_setrec.SInj OldZF.Std_setinf.phSig(@OC.var OB.sig_empty 0)))).
 set(MZ:=E_sf SFMember(names 1)(names 0)).
 set(SZ:=source_parameter_expression names(isolated_formula(OldZF.Std_setrec.Rel2 OldZF.Std_setinf.phSig(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2)))).
 set(APPF:=source_parameter_expression names(isolated_formula(OldZF.Std_setbase.App(@OC.var OB.sig_empty 3)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 4)))).
 set(ADJ:=source_parameter_expression names(isolated_formula(OldZF.Std_setbase.Adj(@OC.var OB.sig_empty 3)(@OC.var OB.sig_empty 5)(@OC.var OB.sig_empty 6)))).
 set(MU:=E_sf SFMember(names 7)(names 0)).
 set(SU:=source_parameter_expression names(isolated_formula(OldZF.Std_setrec.Rel2 OldZF.Std_setinf.phSig(@OC.var OB.sig_empty 7)(@OC.var OB.sig_empty 8)))).
 set(EQ:=E_sf SFEqual(names 8)(names 2)).
 set(APPG:=source_parameter_expression names(isolated_formula(OldZF.Std_setbase.App(@OC.var OB.sig_empty 6)(@OC.var OB.sig_empty 7)(@OC.var OB.sig_empty 4)))).
 change(code_relation M rho(E_sf SFImpl INJ(E_sf SFImpl MZ(E_sf SFImpl SZ(E_sf SFImpl APPF(E_sf SFImpl ADJ(E_sf SFImpl MU(E_sf SFImpl SU(E_sf SFImpl EQ APPG))))))))law)in HG.
 destruct(schema_expression_split M rho SFImpl _ _ law HG)as(inj&t1&HI&HT1&H1).
 destruct(schema_expression_split M rho SFImpl _ _ t1 HT1)as(mz&t2&HMZ&HT2&H2).
 destruct(schema_expression_split M rho SFImpl _ _ t2 HT2)as(sz&t3&HSZ&HT3&H3).
 destruct(schema_expression_split M rho SFImpl _ _ t3 HT3)as(appf&t4&HAppF&HT4&H4).
 destruct(schema_expression_split M rho SFImpl _ _ t4 HT4)as(adj&t5&HAdj&HT5&H5).
 destruct(schema_expression_split M rho SFImpl _ _ t5 HT5)as(mu&t6&HMU&HT6&H6).
 destruct(schema_expression_split M rho SFImpl _ _ t6 HT6)as(su&t7&HSU&HT7&H7).
 destruct(schema_expression_split M rho SFImpl _ _ t7 HT7)as(equal&appg&HE&HAppG&H8).
 exists inj,mz,sz,appf,adj,mu,su,equal,appg.
 split;[exact(source_parameter_rec_injectivity M names rho 0 N inj eq_refl HI)|].
 split;[exact(proj1(schema_expression_graph M rho SFMember(names 1)(names 0)z N mz eq_refl eq_refl)HMZ)|].
 split;[exact(source_parameter_rec_rel2_successor M names rho 1 2 z next sz eq_refl eq_refl HSZ)|].
 split;[exact(source_parameter_rec_app M names rho 3 1 4 f z v appf eq_refl eq_refl eq_refl HAppF)|].
 split;[exact(source_parameter_rec_adjoin M names rho 3 5 6 f q g adj eq_refl eq_refl eq_refl HAdj)|].
 split;[exact(proj1(schema_expression_graph M rho SFMember(names 7)(names 0)u N mu eq_refl eq_refl)HMU)|].
 split;[exact(source_parameter_rec_rel2_successor M names rho 7 8 u nextu su eq_refl eq_refl HSU)|].
 split;[exact(proj1(schema_expression_graph M rho SFEqual(names 8)(names 2)nextu next equal eq_refl eq_refl)HE)|].
 split;[exact(source_parameter_rec_app M names rho 6 7 4 g u v appg eq_refl eq_refl eq_refl HAppG)|].
 rec_pack_telescope.
Qed.
Theorem source_zfr_rec_fresh_predecessor_total M N z next f v q g u nextu:
 exists inj mz sz appf adj mu su equal appg law,
 source_rec_injectivity M N inj /\sf_relation M SFMember z N mz /\source_rec_successor M z next sz /\source_rec_app M f z v appf /\
 source_rec_adjoin M f q g adj /\sf_relation M SFMember u N mu /\source_rec_successor M u nextu su /\sf_relation M SFEqual nextu next equal /\
 source_rec_app M g u v appg /\source_finite_telescope M[inj;mz;sz;appf;adj;mu;su;equal]appg law /\source_zfr_provable M law.
Proof.
 destruct(code_relation_total M source_rec_fresh_predecessor_expression(source_rec_env9 N z next f v q g u nextu))as(law&HG).
 destruct(source_rec_fresh_predecessor_shell M N z next f v q g u nextu law HG)as(inj&mz&sz&appf&adj&mu&su&eq&appg&HI&HMZ&HSZ&HAF&HA&HMU&HSU&HE&HAG&HT).
 exists inj,mz,sz,appf,adj,mu,su,eq,appg,law. split;[exact HI|]. split;[exact HMZ|]. split;[exact HSZ|]. split;[exact HAF|].
 split;[exact HA|]. split;[exact HMU|]. split;[exact HSU|]. split;[exact HE|]. split;[exact HAG|]. split;[exact HT|].
 exact(source_zfr_rec_fresh_predecessor_named M(source_rec_env9 N z next f v q g u nextu)law HG).
Qed.
Print Assumptions source_rec_fresh_predecessor_shell.
Print Assumptions source_zfr_rec_fresh_predecessor_total.
