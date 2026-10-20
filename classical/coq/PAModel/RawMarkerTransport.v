(** Container equality transports the singleton profile. Together with the
    fixed marker exclusions this excludes the two marker containers from
    singleton branches of the tagged matrix. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  ProofTemplates TemplatePropositional ProofMacros QuantifierMacros
  NumericalVacuitySteps NamedLeibnizSteps TemplateFormulaFresh FreshNames
  NumericalKP0 NumericalKP0Eligibility NumericalSingleton NumericalRawPair NumericalTaggedComprehension
  RawMarkerExclusions.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Theorem numerical_singleton_container M rho X P R Z pv rv zv :
  code_relation M rho P pv -> code_relation M rho R rv -> code_relation M rho Z zv ->
  pv<>zv -> rv<>zv ->
  ns_proof M rho (E_wim (E_weq P R)
    (E_wim (E_raw_singleton X P Z) (E_raw_singleton X R Z))).
Proof.
  intros HP HR HZ HPZ HRZ.
  set (H:=E_weq P R).
  set (AP:=E_wim (E_wel Z P) (E_weq Z X)).
  set (AR:=E_wim (E_wel Z R) (E_weq Z X)).
  assert (HBody:ns_proof M rho (E_wim H (E_wim AP AR))).
  { apply (ns_proof_macro M rho
      (E_wim (E_weq P R) (E_weq R P) ::
       E_wim (E_weq R P) (E_wim (E_wel Z R) (E_wel Z P)) :: nil)).
    - intros e [<-|[<-|[]]].
      + apply ns_proof_symmetry.
      + apply marker_membership_transport.
    - unfold H,AP,AR. apply macro_discharge. do 3 apply macro_deduction.
      eapply md_mp with (a:=E_wel Z P).
      + eapply md_mp with (a:=E_wel Z R);[apply md_hyp;now left|].
        eapply md_mp with (a:=E_weq R P).
        * eapply md_mp with (a:=E_weq P R);[apply md_hyp;now right;right;left|].
          apply md_global,PM_input;now left.
        * apply md_global,PM_input;now right;left.
      + apply md_hyp;now right;left. }
  assert (HV:ns_proof M rho (E_vac Z H)).
  { apply (kp0_expression_fresh_vacuity M rho Z H zv HZ).
    unfold H. apply expression_fresh_atom;[now right| |].
    - intros v Hv. rewrite (code_relation_functional M P rho v pv Hv HP). exact HPZ.
    - intros v Hv. rewrite (code_relation_functional M R rho v rv Hv HR). exact HRZ. }
  assert (HAll:ns_proof M rho (E_wim H (E_wim (E_wal Z AP) (E_wal Z AR)))).
  { apply (ns_proof_macro M rho (E_wim H (E_wim AP AR) :: E_vac Z H :: nil)).
    - intros e [<-|[<-|[]]];assumption.
    - apply ns_macro_all. }
  apply (ns_proof_macro M rho
    (E_wim H (E_wim (E_wel X P) (E_wel X R)) ::
     E_wim H (E_wim (E_wal Z AP) (E_wal Z AR)) :: nil)).
  - intros e [<-|[<-|[]]].
    + apply marker_membership_transport.
    + exact HAll.
  - unfold E_raw_singleton. change
      (proof_macro nil (E_wim H (E_wim (E_wel X P) (E_wel X R)) ::
       E_wim H (E_wim (E_wal Z AP) (E_wal Z AR)) :: nil)
       (E_wim H (E_wim (E_wa (E_wel X P) (E_wal Z AP))
         (E_wa (E_wel X R) (E_wal Z AR))))).
    apply macro_discharge. do 2 apply macro_deduction. apply kp0_md_conjunction.
    + eapply md_mp with (a:=E_wel X P).
      * apply tagged_md_left with (b:=E_wal Z AP),md_hyp;now left.
      * eapply md_mp with (a:=H);[apply md_hyp;now right;left|].
        apply md_global,PM_input;now left.
    + eapply md_mp with (a:=E_wal Z AP).
      * apply tagged_md_right with (a:=E_wel X P),md_hyp;now left.
      * eapply md_mp with (a:=H);[apply md_hyp;now right;left|].
        apply md_global,PM_input;now right;left.
Qed.

Theorem numerical_singleton_not_marker M rho T X P Z tv xv pv zv :
  code_relation M rho T tv -> code_relation M rho X xv ->
  code_relation M rho P pv -> code_relation M rho Z zv ->
  zv<>zeroM M -> zv<>xv -> tv<>zv -> pv<>zv ->
  ns_proof M rho (E_wim (E_marker_empty T Z)
    (E_wim (E_raw_singleton X P Z) (E_wn (E_weq P T)))).
Proof.
  intros HT HX HP HZ H0 HZX HTZ HPZ.
  apply (ns_proof_macro M rho
    (E_wim (E_marker_empty T Z) (E_wn (E_raw_singleton X T Z)) ::
     E_wim (E_weq P T) (E_wim (E_raw_singleton X P Z) (E_raw_singleton X T Z)) :: nil)).
  - intros e [<-|[<-|[]]].
    + exact (numerical_empty_not_singleton M rho T X Z tv xv zv HT HX HZ H0 HZX HTZ).
    + exact (numerical_singleton_container M rho X P T Z pv tv zv HP HT HZ HPZ HTZ).
  - apply macro_discharge. do 3 apply macro_deduction.
    eapply md_mp with (a:=E_raw_singleton X T Z).
    + eapply md_mp with (a:=E_raw_singleton X P Z);[apply md_hyp;now right;left|].
      eapply md_mp with (a:=E_weq P T);[apply md_hyp;now left|].
      apply md_global,PM_input;now right;left.
    + eapply md_mp with (a:=E_marker_empty T Z);[apply md_hyp;now right;right;left|].
      apply md_global,PM_input;now left.
Qed.

Theorem numerical_singleton_not_pair M rho B T R X P Z bv tv rv xv pv zv :
  code_relation M rho B bv -> code_relation M rho T tv -> code_relation M rho R rv ->
  code_relation M rho X xv -> code_relation M rho P pv -> code_relation M rho Z zv ->
  zv<>bv -> zv<>tv -> rv<>zv -> xv<>zv -> pv<>zv ->
  ns_proof M rho (E_wim (E_wn (E_weq B T)) (E_wim (E_raw_pair B T R Z)
    (E_wim (E_raw_singleton X P Z) (E_wn (E_weq P R))))).
Proof.
  intros HB HT HR HX HP HZ HZB HZT HRZ HXZ HPZ.
  apply (ns_proof_macro M rho
    (E_wim (E_wn (E_weq B T)) (E_wim (E_raw_pair B T R Z) (E_wn (E_raw_singleton X R Z))) ::
     E_wim (E_weq P R) (E_wim (E_raw_singleton X P Z) (E_raw_singleton X R Z)) :: nil)).
  - intros e [<-|[<-|[]]].
    + exact (numerical_pair_not_singleton M rho B T R X Z bv tv rv xv zv HB HT HR HX HZ HZB HZT HRZ HXZ).
    + exact (numerical_singleton_container M rho X P R Z pv rv zv HP HR HZ HPZ HRZ).
  - apply macro_discharge. do 4 apply macro_deduction.
    eapply md_mp with (a:=E_raw_singleton X R Z).
    + eapply md_mp with (a:=E_raw_singleton X P Z);[apply md_hyp;now right;left|].
      eapply md_mp with (a:=E_weq P R);[apply md_hyp;now left|].
      apply md_global,PM_input;now right;left.
    + eapply md_mp with (a:=E_raw_pair B T R Z);[apply md_hyp;now right;right;left|].
      eapply md_mp with (a:=E_wn (E_weq B T));[apply md_hyp;now right;right;right;left|].
      apply md_global,PM_input;now left.
Qed.

Print Assumptions numerical_singleton_container.
Print Assumptions numerical_singleton_not_marker.
Print Assumptions numerical_singleton_not_pair.
