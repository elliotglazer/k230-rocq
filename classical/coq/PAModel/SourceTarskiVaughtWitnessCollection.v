(** Actual common-context assembly of every witness-closure requirement.
    The hypotheses are literal descriptor proofs of a fixed geometry
    telescope, not an assumption that proof preservation is available. *)
From PAModel Require Import Model FiniteCoding FiniteCRT Pairing NumericalContexts NumericalSourceFull
  SourcePieceWitnessInstance SourcePieceWitnessTables SourceTelescopeOutputTables
  SourceFiniteTelescope SourceInternalProofContexts SourceAxiomContexts SourceDescriptorProvability
  SourceProofWeakening SourceQuantifierPieces SourcePCSPieces SourcePCSTables SourceTarskiVaughtInputs.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Definition source_piece_witness_telescope_table M domain Y A sb sc count ob oc:=
  forall i entry pc piece law,coding_lt M i count ->beta M sb sc i entry ->
    pair_graph M pc piece entry ->beta M ob oc i law ->
    exists wh,source_piece_witness_instance M domain pc piece Y wh /\
      source_finite_telescope M A wh law.

Theorem source_piece_witness_telescope_table_total M domain Y A sb sc count:
  exists ob oc,source_piece_witness_telescope_table M domain Y A sb sc count ob oc.
Proof.
  destruct(source_piece_witness_table_total M domain Y sb sc count)as(wb&wc&HW).
  destruct(source_telescope_output_table_total M A wb wc count)as(ob&oc&HO).
  exists ob,oc. intros i entry pc piece law HI HE HP HL.
  destruct(beta_total M wb wc i)as(wh&HWh).
  exists wh. split;[exact(HW i entry pc piece wh HI HE HP HWh)|].
  exact(HO i wh law HI HWh HL).
Qed.

Theorem source_descriptor_piece_witness_telescope_context M T domain Y A sb sc count:
  (forall entry pc piece wh law,context_member M sb sc count entry ->
    pair_graph M pc piece entry ->source_piece_witness_instance M domain pc piece Y wh ->
    source_finite_telescope M A wh law ->source_descriptor_provable M T law) ->
  exists b c n,source_axiom_context M T b c n /\
    forall entry pc piece wh,context_member M sb sc count entry ->
      pair_graph M pc piece entry ->source_piece_witness_instance M domain pc piece Y wh ->
      exists law,source_finite_telescope M A wh law /\source_full_prv M b c n law.
Proof.
  intro HP.
  destruct(source_piece_witness_telescope_table_total M domain Y A sb sc count)as(ob&oc&HT).
  assert(HLocal:forall law,context_member M ob oc count law ->source_descriptor_provable M T law).
  { intros law(i&HI&HL). destruct(beta_total M sb sc i)as(entry&HE).
    destruct(pair_surjective M entry)as(pc&piece&HPair).
    destruct(HT i entry pc piece law HI HE HPair HL)as(wh&HWh&HTel).
    exact(HP entry pc piece wh law(ex_intro _ i(conj HI HE))HPair HWh HTel). }
  destruct(source_descriptor_internal_common_context M T ob oc count HLocal)as(b&c&n&HC&P).
  exists b,c,n. split;[exact HC|].
  intros entry pc piece wh(i&HI&HE)HPair HWh.
  destruct(beta_total M ob oc i)as(law&HL).
  destruct(HT i entry pc piece law HI HE HPair HL)as(wh'&HWh'&HTel).
  pose proof(source_piece_witness_instance_functional M domain pc piece Y wh wh' HWh HWh')as E.
  subst wh'. exists law. split;[exact HTel|]. exact(P law(ex_intro _ i(conj HI HL))).
Qed.

Theorem source_descriptor_tv_witnesses_common_context M T domain phi count Y A sb sc pieces:
  source_pcs_table M domain phi count sb sc pieces ->
  (forall pc body piece wh law,source_quantifier_body M phi count pc body ->
    source_pcs_sign M domain body piece ->source_piece_witness_instance M domain pc piece Y wh ->
    source_finite_telescope M A wh law ->source_descriptor_provable M T law) ->
  exists b c n,source_axiom_context M T b c n /\
    forall ub uc un k,context_included M b c n ub uc un ->context_bounded M ub uc un k ->
      (forall a,In a A ->source_full_prv M ub uc un a) ->
      source_tv_witnesses M domain phi count Y ub uc un.
Proof.
  intros HTable HP.
  assert(HLocal:forall entry pc piece wh law,context_member M sb sc pieces entry ->
    pair_graph M pc piece entry ->source_piece_witness_instance M domain pc piece Y wh ->
    source_finite_telescope M A wh law ->source_descriptor_provable M T law).
  { intros entry pc piece wh law HE HPair HWh HTel.
    destruct(proj1(HTable entry)HE)as(pc'&body&piece'&HBody&HSign&HPair').
    destruct(pair_injective M entry pc piece pc' piece' HPair HPair')as(Epc&Epiece).
    subst pc' piece'. exact(HP pc body piece wh law HBody HSign HWh HTel). }
  destruct(source_descriptor_piece_witness_telescope_context M T domain Y A sb sc pieces HLocal)
    as(b&c&n&HC&P).
  exists b,c,n. split;[exact HC|].
  intros ub uc un k HIncl BC PA pc body piece wh HBody HSign HWh.
  destruct(pair_total M pc piece)as(entry&HPair).
  assert(HE:context_member M sb sc pieces entry).
  { apply(proj2(HTable entry)). exists pc,body,piece. auto. }
  destruct(P entry pc piece wh HE HPair HWh)as(law&HTel&PLaw).
  exact(source_full_finite_telescope_apply M A wh law HTel ub uc un
    (source_full_prv_weaken_bounded M b c n ub uc un law k PLaw HIncl BC)PA).
Qed.

Print Assumptions source_piece_witness_telescope_table_total.
Print Assumptions source_descriptor_piece_witness_telescope_context.
Print Assumptions source_descriptor_tv_witnesses_common_context.
