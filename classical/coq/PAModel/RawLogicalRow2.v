(** Uniform actual image of the machine's universal distribution row.
    The arbitrary raw matrices are translated internally, including zero. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension
  CodeExpressions CodeDescent NumericalProofs ProofTemplates SetFormulaCodes SetCodeDescent
  SourceBounded SourceBoundMonotone NumericalRenaming SourceRenamingBounds RawBinderRenaming
  RawSourceImage RawSourceImageInversion RawSourceImageBounds RawSourcePropositional
  RawFinitePropositional RawEqualityCalibration SourceUniversalDistribution
  SourceZFCProvability SourceZFCBasicClosure.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.

Lemma raw_universal_nonzero M x a f : universal_graph M x a f -> f<>zeroM M.
Proof.
  intro HF. exact (raw_positive_tag_nonzero M 2 x a f ltac:(lia)
    (proj1 (universal_graph_tagged M x a f) HF)).
Qed.

Theorem raw_distribution_graph_source M x b c h qh qb qc inside raw out :
  implication_graph M b c h -> universal_graph M x h qh ->
  universal_graph M x b qb -> universal_graph M x c qc ->
  implication_graph M qb qc inside -> implication_graph M qh inside raw ->
  raw_source_image M raw out -> source_zfc_provable M out.
Proof.
  intros HI HQH HQB HQC HIn HRaw HOut.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) h) as [EH|[hp EH]].
  - subst h. destruct (raw_zero_implication_arguments M b c HI) as [EB EC].
    subst b c. assert (E:qb=qc).
    { apply (code_relation_functional M (E_wal (CEvar 0) (CEvar 1))
        (arguments2 x (zeroM M) (zeroM M)));assumption. }
    subst qc. apply source_zfc_provable_from_empty.
    apply (raw_prop_certificate_empty_source M raw out);[|exact HOut].
    apply (rpc_intro M [] qh inside raw HRaw).
    apply (rpc_intro M [qh] qb qb inside HIn). apply rpc_hyp. cbn. auto.
  - assert (HN:h<>zeroM M).
    { change (h=succM M hp) in EH. intro E. apply (zero_ne_succ M hp). congruence. }
    pose proof (raw_implication_nonzero_consequent M qb qc inside
      (raw_universal_nonzero M x c qc HQC) HIn) as HInN.
    pose proof (raw_implication_nonzero_consequent M qh inside raw HInN HRaw) as HRawN.
    destruct (raw_source_implication_inv M qh inside raw out HRawN HRaw HOut)
      as (sqh&sin&HQHI&HInI&HSOut).
    destruct (raw_source_implication_inv M qb qc inside sin HInN HIn HInI)
      as (sqb&sqc&HQBI&HQCI&HSIn).
    destruct (raw_source_universal_inv M x h qh sqh HQH HQHI)
      as (sh&rb&rc&vh&HHI&HMap&HRenameH&HQSimp).
    destruct (raw_source_implication_inv M b c h sh HN HI HHI)
      as (sb&sc&HBI&HCI&HSImp).
    apply (proj1 (numerical_renaming_binary M SFImpl sb sc sh rb rc (succM M x)
      (succM M (zeroM M)) vh ltac:(unfold sf_binary;auto) HSImp)) in HRenameH.
    destruct HRenameH as (vb&vc&HRB&HRC&HRImpl).
    destruct (raw_source_universal_inv M x b qb sqb HQB HQBI)
      as (sb'&rb'&rc'&vb'&HBI'&HMapB&HRB'&HQSb).
    rewrite (raw_source_image_functional M b sb' sb HBI' HBI) in HRB'.
    assert (EVB:vb'=vb).
    { exact (numerical_renaming_functional_equivalent M sb rb' rc' (succM M x) rb rc (succM M x)
        (succM M (zeroM M)) vb' vb
        (raw_binder_renaming_equivalent M x rb' rc' rb rc HMapB HMap) HRB' HRB). }
    subst vb'.
    destruct (raw_source_universal_inv M x c qc sqc HQC HQCI)
      as (sc'&rb''&rc''&vc'&HCI'&HMapC&HRC'&HQSc).
    rewrite (raw_source_image_functional M c sc' sc HCI' HCI) in HRC'.
    assert (EVC:vc'=vc).
    { exact (numerical_renaming_functional_equivalent M sc rb'' rc'' (succM M x) rb rc (succM M x)
        (succM M (zeroM M)) vc' vc
        (raw_binder_renaming_equivalent M x rb'' rc'' rb rc HMapC HMap) HRC' HRC). }
    subst vc'.
    destruct (raw_source_image_bounded M qb sqb HQBI) as [kb HBb].
    destruct (raw_source_image_bounded M qc sqc HQCI) as [kc HBc].
    apply (proj1 (source_bounded_accept_unary M SFAll vb sqb kb (or_introl eq_refl) HQSb)) in HBb.
    apply (proj1 (source_bounded_accept_unary M SFAll vc sqc kc (or_introl eq_refl) HQSc)) in HBc.
    set (k:=addM M (succM M kb) (succM M kc)).
    assert (HBb':source_bounded M vb k).
    { exact (source_bounded_monotone M vb (succM M kb) k HBb
        (coding_le_add M (succM M kb) (succM M kc))). }
    assert (HBc':source_bounded M vc k).
    { apply (source_bounded_monotone M vc (succM M kc) k HBc).
      unfold k. rewrite Arithmetic.add_comm. apply coding_le_add. }
    apply source_zfc_provable_from_empty.
    exact (source_universal_distribution M vb vc vh sqb sqc sqh sin out k
      HBb' HBc' HRImpl HQSb HQSc HQSimp HSIn HSOut).
Qed.

Theorem source_zfc_raw_row2 M env raw out :
  code_relation M env code_row2 raw -> raw_source_image M raw out -> source_zfc_provable M out.
Proof.
  intros HR HO.
  destruct (code_relation_total M (E_wim (CEvar 1) (CEvar 2)) env) as [h HH].
  destruct (code_relation_total M (E_wal (CEvar 0) (E_wim (CEvar 1) (CEvar 2))) env) as [qh HQH].
  destruct (code_relation_total M (E_wal (CEvar 0) (CEvar 1)) env) as [qb HQB].
  destruct (code_relation_total M (E_wal (CEvar 0) (CEvar 2)) env) as [qc HQC].
  destruct (code_relation_total M (E_wim (E_wal (CEvar 0) (CEvar 1))
    (E_wal (CEvar 0) (CEvar 2))) env) as [inside HIn].
  apply (raw_distribution_graph_source M (env 0) (env 1) (env 2) h qh qb qc inside raw out).
  - exact (expression_implication_graph M env (CEvar 1) (CEvar 2) _ _ h eq_refl eq_refl HH).
  - exact (expression_universal_graph M env (CEvar 0) (E_wim (CEvar 1) (CEvar 2)) _ h qh eq_refl HH HQH).
  - exact (expression_universal_graph M env (CEvar 0) (CEvar 1) _ _ qb eq_refl eq_refl HQB).
  - exact (expression_universal_graph M env (CEvar 0) (CEvar 2) _ _ qc eq_refl eq_refl HQC).
  - exact (expression_implication_graph M env (E_wal (CEvar 0) (CEvar 1))
      (E_wal (CEvar 0) (CEvar 2)) qb qc inside HQB HQC HIn).
  - exact (expression_implication_graph M env (E_wal (CEvar 0) (E_wim (CEvar 1) (CEvar 2)))
      (E_wim (E_wal (CEvar 0) (CEvar 1)) (E_wal (CEvar 0) (CEvar 2))) qh inside raw HQH HIn HR).
  - exact HO.
Qed.

Print Assumptions raw_distribution_graph_source.
Print Assumptions source_zfc_raw_row2.
