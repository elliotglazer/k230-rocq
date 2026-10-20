(** Interpretation of every successful finite public runtime certificate.
    Concrete Box head/oracle evidence remains explicit at this generic layer. *)
From PAModel Require Import Model CodeExpressions TM230Paths TM230MacroProgress TM230RuntimeWords
 TM230RuntimeStep TM230PositiveComposition.
From K230 Require Runtime230Core.
From Stdlib Require Import Bool.Bool.
Unset Implicit Arguments.
Theorem machine230_runtime_exec_sound M gap Box br
 (Hhead:forall x word,Box x word->exists tail,word=mulM M(code_numeral M 2)tail)
 (Horacle:machine230_runtime_oracle_paths M Box br)fuel target:
 forall conf moved conf' s,Runtime230.exec fuel br target conf moved=Some conf' ->
 machine230_runtime_view M gap Box conf s ->
 target conf'=true /\exists t,machine230_runtime_view M gap Box conf' t /\machine230_reaches M s t /\
 (moved=false->machine230_progresses M s t).
Proof.
 induction fuel as[|fuel IH];intros conf moved conf' s HE HV;[discriminate|].
 cbn[Runtime230.exec]in HE. destruct(if moved then target conf else false)eqn:HT.
 -injection HE as <-. destruct moved;[|discriminate].
  split;[exact HT|]. exists s;split;[exact HV|]. split;[apply machine230_reaches_refl|discriminate].
 -destruct(Runtime230.sstep br conf)as[[next flag]|]eqn:HS;[|discriminate].
  destruct(machine230_runtime_sstep_sound M gap Box br Hhead Horacle conf next flag s HS HV)
   as[u[HU[H0 P0]]].
  destruct(IH next(orb moved flag)conf' u HE HU)as[HG[t[HTV[H1 P1]]]].
  split;[exact HG|]. exists t;split;[exact HTV|]. split.
  +eapply machine230_reaches_trans;eassumption.
  +intros ->. destruct flag.
   *eapply machine230_progresses_reaches_trans;[exact(P0 eq_refl)|exact H1].
   *eapply machine230_reaches_progresses_trans;[exact H0|exact(P1 eq_refl)].
Qed.
Print Assumptions machine230_runtime_exec_sound.

