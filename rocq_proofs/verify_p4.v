From Stdlib Require Import Bool List Arith Lia Classical.
Import ListNotations.

(* ========================================================================= *)
(* Formal Verification in Rocq (Coq) of the 4-QBF <-> Classifier Existential *)
(* Fairness Reduction (Pi_4^P-completeness of P4, closing the final open     *)
(* problem of Section 7 / Proposition 28 of Cooper & Bousdira, CP 2026).     *)
(* ========================================================================= *)

Definition lit := (nat * bool)%type.
Definition clause := list lit.
Definition cnf := list clause.

Definition eval_lit (assign : nat -> bool) (l : lit) : bool :=
  Bool.eqb (assign (fst l)) (snd l).

Fixpoint eval_clause (assign : nat -> bool) (c : clause) : bool :=
  match c with
  | [] => false
  | l :: rest => eval_lit assign l || eval_clause assign rest
  end.

Fixpoint eval_cnf (assign : nat -> bool) (phi : cnf) : bool :=
  match phi with
  | [] => true
  | c :: rest => eval_clause assign c && eval_cnf assign rest
  end.

Definition cnf_bounded (n : nat) (phi : cnf) : Prop :=
  forall c, In c phi -> forall l, In l c -> fst l < n.

Lemma eval_clause_ext_bounded : forall n c f g,
  (forall l, In l c -> fst l < n) ->
  (forall k, k < n -> f k = g k) ->
  eval_clause f c = eval_clause g c.
Proof.
  intros n c f g Hc Hext.
  induction c as [|l cs IHc]; simpl; [reflexivity|].
  f_equal.
  - unfold eval_lit. rewrite Hext; [reflexivity | apply Hc; left; reflexivity].
  - apply IHc. intros l' Hl'. apply Hc; right; exact Hl'.
Qed.

Lemma eval_cnf_ext_bounded : forall n phi f g,
  cnf_bounded n phi ->
  (forall k, k < n -> f k = g k) ->
  eval_cnf f phi = eval_cnf g phi.
Proof.
  intros n phi f g Hbnd Hext.
  induction phi as [|c rest IH]; simpl; [reflexivity|].
  f_equal.
  - apply (eval_clause_ext_bounded n c f g); [|exact Hext].
    intros l Hl. apply (Hbnd c (or_introl eq_refl) l Hl).
  - apply IH. intros c' Hc' l Hl. apply (Hbnd c' (or_intror Hc') l Hl).
Qed.

Definition combine4 (t r q : nat) (W X Y Z : nat -> bool) (k : nat) : bool :=
  if k <? t then W k
  else if k <? t + r then X (k - t)
  else if k <? t + r + q then Y (k - (t + r))
  else Z (k - (t + r + q)).

Lemma combine4_ext : forall t r q s W1 W2 X1 X2 Y1 Y2 Z1 Z2 k,
  k < t + r + q + s ->
  (forall m, m < t -> W1 m = W2 m) ->
  (forall i, i < r -> X1 i = X2 i) ->
  (forall j, j < q -> Y1 j = Y2 j) ->
  (forall m, m < s -> Z1 m = Z2 m) ->
  combine4 t r q W1 X1 Y1 Z1 k = combine4 t r q W2 X2 Y2 Z2 k.
Proof.
  intros t r q s W1 W2 X1 X2 Y1 Y2 Z1 Z2 k Hk HW HX HY HZ.
  unfold combine4.
  destruct (Nat.ltb_spec k t); [apply HW; lia|].
  destruct (Nat.ltb_spec k (t + r)); [apply HX; lia|].
  destruct (Nat.ltb_spec k (t + r + q)); [apply HY; lia|].
  apply HZ; lia.
Qed.

(* Standard Pi_4^P 4-QBF: forall W, exists X, forall Y, exists Z, Phi(W,X,Y,Z) = true *)
Definition four_qbf (t r q : nat) (phi : cnf) : Prop :=
  forall W : nat -> bool, exists X : nat -> bool,
  forall Y : nat -> bool, exists Z : nat -> bool,
    eval_cnf (combine4 t r q W X Y Z) phi = true.

Record Inst := mkInst {
  fd : bool;
  fqB : bool;
  fz0 : bool;
  fWp : nat -> bool;
  fWm : nat -> bool;
  fXp : nat -> bool;
  fXm : nat -> bool;
  fYp : nat -> bool;
  fYm : nat -> bool;
  fZ : nat -> bool;
  fp : bool
}.

Record Sub := mkSub {
  sd : bool;
  sqB : bool;
  sz0 : bool;
  sWp : nat -> bool;
  sWm : nat -> bool;
  sXp : nat -> bool;
  sXm : nat -> bool;
  sYp : nat -> bool;
  sYm : nat -> bool;
  sZ : nat -> bool;
  sp : bool
}.

(* In the Looseness-Shielded P4 reduction, P = {p^*} is the unique protected feature *)
Definition is_fair_P4 (S : Sub) : Prop := sp S = false.
Definition is_unfair_P4 (T : Sub) : Prop := sp T = true.

Definition agrees_on (t r q s : nat) (w x : Inst) (S : Sub) : Prop :=
  (sd S = true -> fd w = fd x) /\
  (sqB S = true -> fqB w = fqB x) /\
  (sz0 S = true -> fz0 w = fz0 x) /\
  (forall k, k < t -> sWp S k = true -> fWp w k = fWp x k) /\
  (forall k, k < t -> sWm S k = true -> fWm w k = fWm x k) /\
  (forall i, i < r -> sXp S i = true -> fXp w i = fXp x i) /\
  (forall i, i < r -> sXm S i = true -> fXm w i = fXm x i) /\
  (forall j, j < q -> sYp S j = true -> fYp w j = fYp x j) /\
  (forall j, j < q -> sYm S j = true -> fYm w j = fYm x j) /\
  (forall m, m < s -> sZ S m = true -> fZ w m = fZ x m) /\
  (sp S = true -> fp w = fp x).

Lemma agrees_on_refl : forall t r q s x S, agrees_on t r q s x x S.
Proof.
  intros t r q s x S. repeat split; intros; reflexivity.
Qed.

Fixpoint forall_nat (n : nat) (P : nat -> bool) : bool :=
  match n with
  | 0 => true
  | S m => P m && forall_nat m P
  end.

Lemma forall_nat_iff : forall n P,
  forall_nat n P = true <-> (forall i, i < n -> P i = true).
Proof.
  induction n as [|m IH]; intro P; simpl.
  - split; [intros _ i Hi; lia | intros _; reflexivity].
  - rewrite Bool.andb_true_iff, IH. split.
    + intros [Hm Hrest] i Hi.
      destruct (Nat.eq_dec i m); [subst; exact Hm | apply Hrest; lia].
    + intro H. split; [apply H; lia | intros i Hi; apply H; lia].
Qed.

Lemma forall_nat_true : forall n P,
  (forall i, i < n -> P i = true) -> forall_nat n P = true.
Proof. intros n P. apply (proj2 (forall_nat_iff n P)). Qed.

Lemma forall_nat_elim : forall n P,
  forall_nat n P = true -> forall i, i < n -> P i = true.
Proof. intros n P. apply (proj1 (forall_nat_iff n P)). Qed.

Lemma forall_nat_false_exists : forall n P,
  forall_nat n P = false -> exists i, i < n /\ P i = false.
Proof.
  induction n as [|m IH]; intros P H; simpl in H.
  - discriminate.
  - apply Bool.andb_false_iff in H. destruct H as [Hm | Hrest].
    + exists m. split; [lia | exact Hm].
    + destruct (IH P Hrest) as [i [Hi HPi]]. exists i. split; [lia | exact HPi].
Qed.

Lemma forall_nat_ext : forall n P Q,
  (forall i, i < n -> P i = Q i) -> forall_nat n P = forall_nat n Q.
Proof.
  induction n as [|m IH]; intros P Q H; simpl; [reflexivity|].
  rewrite (H m ltac:(lia)), (IH P Q (fun i Hi => H i ltac:(lia))). reflexivity.
Qed.

Definition w_ok (t : nat) (w : Inst) : bool :=
  forall_nat t (fun k => fWp w k || fWm w k).

Definition x_ok (r : nat) (w : Inst) : bool :=
  forall_nat r (fun i => fXp w i || fXm w i).

Definition w_uniq (t : nat) (w : Inst) : bool :=
  forall_nat t (fun k => Bool.eqb (fWp w k) (negb (fWm w k))).

Definition x_uniq (r : nat) (w : Inst) : bool :=
  forall_nat r (fun i => Bool.eqb (fXp w i) (negb (fXm w i))).

Definition y_uniq (q : nat) (w : Inst) : bool :=
  forall_nat q (fun j => Bool.eqb (fYp w j) (negb (fYm w j))).

Definition all_X_true (r : nat) (w : Inst) : bool :=
  forall_nat r (fun i => fXp w i && fXm w i).

Definition all_Y_true (q : nat) (w : Inst) : bool :=
  forall_nat q (fun j => fYp w j && fYm w j).

Definition is_dummy (t r q : nat) (w : Inst) : bool :=
  negb (fp w) && w_ok t w && all_X_true r w && all_Y_true q w.

Definition is_phi (t r q : nat) (w : Inst) : bool :=
  w_uniq t w && x_uniq r w && y_uniq q w.

Definition C_p4 (t r q : nat) (w : Inst) : bool :=
  if fd w then
    fp w && all_Y_true q w &&
    (if w_ok t w && x_ok r w then
       if w_uniq t w && all_X_true r w then negb (fqB w) else fqB w
     else negb (fqB w))
  else
    negb (fqB w) && (is_dummy t r q w || is_phi t r q w).

Definition kappa_p4 (t r q : nat) (phi : cnf) (w : Inst) : bool :=
  if fd w then
    w_ok t w && x_ok r w
  else
    if is_phi t r q w then
      if fz0 w then
        negb (eval_cnf (combine4 t r q (fWp w) (fXp w) (fYp w) (fZ w)) phi)
      else true
    else false.

(* Literal Definition 14: Constrained FTU *)
Definition constrained_ftu (t r q s : nat) (phi : cnf) : Prop :=
  forall u v : Inst,
    C_p4 t r q u = true ->
    C_p4 t r q v = true ->
    fd u = fd v ->
    fqB u = fqB v ->
    fz0 u = fz0 v ->
    (forall k, k < t -> fWp u k = fWp v k) ->
    (forall k, k < t -> fWm u k = fWm v k) ->
    (forall i, i < r -> fXp u i = fXp v i) ->
    (forall i, i < r -> fXm u i = fXm v i) ->
    (forall j, j < q -> fYp u j = fYp v j) ->
    (forall j, j < q -> fYm u j = fYm v j) ->
    (forall m, m < s -> fZ u m = fZ v m) ->
    kappa_p4 t r q phi u = kappa_p4 t r q phi v.

Theorem p4_constrained_ftu : forall t r q s phi,
  cnf_bounded (t + r + q + s) phi ->
  constrained_ftu t r q s phi.
Proof.
  intros t r q s phi Hbnd u v _ _ Hd HqB Hz0 HWA HWB HA HB HY HYb HZ.
  unfold kappa_p4. rewrite Hd, Hz0.
  assert (Ewok : w_ok t u = w_ok t v).
  { unfold w_ok. apply forall_nat_ext. intros k Hk. rewrite (HWA k Hk), (HWB k Hk). reflexivity. }
  assert (Exok : x_ok r u = x_ok r v).
  { unfold x_ok. apply forall_nat_ext. intros i Hi. rewrite (HA i Hi), (HB i Hi). reflexivity. }
  assert (Ewu : w_uniq t u = w_uniq t v).
  { unfold w_uniq. apply forall_nat_ext. intros k Hk. rewrite (HWA k Hk), (HWB k Hk). reflexivity. }
  assert (Exu : x_uniq r u = x_uniq r v).
  { unfold x_uniq. apply forall_nat_ext. intros i Hi. rewrite (HA i Hi), (HB i Hi). reflexivity. }
  assert (Eyu : y_uniq q u = y_uniq q v).
  { unfold y_uniq. apply forall_nat_ext. intros j Hj. rewrite (HY j Hj), (HYb j Hj). reflexivity. }
  unfold is_phi. rewrite Ewok, Exok, Ewu, Exu, Eyu.
  destruct (fd v); [reflexivity|].
  destruct (w_uniq t v && x_uniq r v && y_uniq q v); [|reflexivity].
  destruct (fz0 v); [|reflexivity].
  f_equal. apply (eval_cnf_ext_bounded (t + r + q + s) phi _ _ Hbnd).
  intros k Hk. apply (combine4_ext t r q s); assumption.
Qed.

(* Literal Definitions 3, 4, 5, 15 *)
Definition sub_le (t r q s : nat) (S1 S2 : Sub) : Prop :=
  (sd S1 = true -> sd S2 = true) /\
  (sqB S1 = true -> sqB S2 = true) /\
  (sz0 S1 = true -> sz0 S2 = true) /\
  (forall k, k < t -> sWp S1 k = true -> sWp S2 k = true) /\
  (forall k, k < t -> sWm S1 k = true -> sWm S2 k = true) /\
  (forall i, i < r -> sXp S1 i = true -> sXp S2 i = true) /\
  (forall i, i < r -> sXm S1 i = true -> sXm S2 i = true) /\
  (forall j, j < q -> sYp S1 j = true -> sYp S2 j = true) /\
  (forall j, j < q -> sYm S1 j = true -> sYm S2 j = true) /\
  (forall m, m < s -> sZ S1 m = true -> sZ S2 m = true) /\
  (sp S1 = true -> sp S2 = true).

Definition sub_strict_lt (t r q s : nat) (S1 S2 : Sub) : Prop :=
  sub_le t r q s S1 S2 /\
  ((sd S2 = true /\ sd S1 = false) \/
   (sqB S2 = true /\ sqB S1 = false) \/
   (sz0 S2 = true /\ sz0 S1 = false) \/
   (exists k, k < t /\ sWp S2 k = true /\ sWp S1 k = false) \/
   (exists k, k < t /\ sWm S2 k = true /\ sWm S1 k = false) \/
   (exists i, i < r /\ sXp S2 i = true /\ sXp S1 i = false) \/
   (exists i, i < r /\ sXm S2 i = true /\ sXm S1 i = false) \/
   (exists j, j < q /\ sYp S2 j = true /\ sYp S1 j = false) \/
   (exists j, j < q /\ sYm S2 j = true /\ sYm S1 j = false) \/
   (exists m, m < s /\ sZ S2 m = true /\ sZ S1 m = false) \/
   (sp S2 = true /\ sp S1 = false)).

Definition weak_axp (t r q s : nat) (phi : cnf) (x : Inst) (S : Sub) : Prop :=
  forall w : Inst, C_p4 t r q w = true -> agrees_on t r q s w x S ->
    kappa_p4 t r q phi w = kappa_p4 t r q phi x.

Definition is_axp (t r q s : nat) (phi : cnf) (x : Inst) (S : Sub) : Prop :=
  weak_axp t r q s phi x S /\
  forall S' : Sub, sub_strict_lt t r q s S' S -> ~ weak_axp t r q s phi x S'.

Definition strictly_subsumes (t r q s : nat) (x : Inst) (T S : Sub) : Prop :=
  (forall u : Inst, C_p4 t r q u = true -> agrees_on t r q s u x S -> agrees_on t r q s u x T) /\
  (exists v : Inst, C_p4 t r q v = true /\ agrees_on t r q s v x T /\ ~ agrees_on t r q s v x S).

Definition is_pi (t r q s : nat) (phi : cnf) (x : Inst) (S : Sub) : Prop :=
  is_axp t r q s phi x S /\
  forall T : Sub, is_axp t r q s phi x T -> ~ strictly_subsumes t r q s x T S.

Definition dec_exist_fair_at (t r q s : nat) (phi : cnf) (x : Inst) : Prop :=
  exists S : Sub,
    is_fair_P4 S /\
    weak_axp t r q s phi x S /\
    forall T : Sub, is_unfair_P4 T -> weak_axp t r q s phi x T ->
      ~ strictly_subsumes t r q s x T S.

Definition cls_exist_fair (t r q s : nat) (phi : cnf) : Prop :=
  forall x : Inst, C_p4 t r q x = true -> dec_exist_fair_at t r q s phi x.

Definition cls_exist_fair_pi (t r q s : nat) (phi : cnf) : Prop :=
  forall x : Inst, C_p4 t r q x = true ->
    exists S : Sub, is_fair_P4 S /\ is_pi t r q s phi x S.

(* ========================================================================= *)
(* Helper Lemmas for Direction 1 (four_qbf -> cls_exist_fair)                *)
(* ========================================================================= *)

Lemma w_uniq_implies_w_ok : forall t w,
  w_uniq t w = true -> w_ok t w = true.
Proof.
  intros t w H. unfold w_ok. apply forall_nat_true. intros k Hk.
  pose proof (forall_nat_elim t _ H k Hk) as H0. simpl in H0.
  destruct (fWp w k); destruct (fWm w k); simpl in *; try discriminate; reflexivity.
Qed.

Lemma x_uniq_implies_x_ok : forall r w,
  x_uniq r w = true -> x_ok r w = true.
Proof.
  intros r w H. unfold x_ok. apply forall_nat_true. intros i Hi.
  pose proof (forall_nat_elim r _ H i Hi) as H0. simpl in H0.
  destruct (fXp w i); destruct (fXm w i); simpl in *; try discriminate; reflexivity.
Qed.

Lemma all_AB_implies_x_ok : forall r w,
  all_X_true r w = true -> x_ok r w = true.
Proof.
  intros r w H. unfold x_ok. apply forall_nat_true. intros i Hi.
  pose proof (forall_nat_elim r _ H i Hi) as H0. simpl in H0.
  apply Bool.andb_true_iff in H0. destruct H0 as [HA _]. rewrite HA. reflexivity.
Qed.

Lemma C_p4_flip_z0 : forall t r q x,
  C_p4 t r q (mkInst (fd x) (fqB x) (negb (fz0 x)) (fWp x) (fWm x) (fXp x) (fXm x) (fYp x) (fYm x) (fZ x) (fp x)) =
  C_p4 t r q x.
Proof.
  intros t r q x. reflexivity.
Qed.

Lemma C_p4_set_z0_false : forall t r q v,
  C_p4 t r q (mkInst (fd v) (fqB v) false (fWp v) (fWm v) (fXp v) (fXm v) (fYp v) (fYm v) (fZ v) (fp v)) =
  C_p4 t r q v.
Proof.
  intros t r q v. reflexivity.
Qed.

Lemma is_phi_set_z0_false : forall t r q v,
  is_phi t r q (mkInst (fd v) (fqB v) false (fWp v) (fWm v) (fXp v) (fXm v) (fYp v) (fYm v) (fZ v) (fp v)) =
  is_phi t r q v.
Proof.
  intros t r q v. reflexivity.
Qed.

(* Case 1: fd x = false /\ is_phi t r q x = true (Looseness Shield!) *)
Definition S_all_N : Sub :=
  mkSub true true true
        (fun _ => true) (fun _ => true)
        (fun _ => true) (fun _ => true)
        (fun _ => true) (fun _ => true)
        (fun _ => true) false.

Lemma case_d0_phi : forall t r q s phi x,
  cnf_bounded (t + r + q + s) phi ->
  C_p4 t r q x = true ->
  fd x = false ->
  is_phi t r q x = true ->
  dec_exist_fair_at t r q s phi x.
Proof.
  intros t r q s phi x Hbnd HxC Exd Exphi.
  exists S_all_N. split; [reflexivity|]. split.
  - intros w HwC [Hd [HqB [Hz0 [HWA [HWB [HA [HB [HY [HYb [HZ _]]]]]]]]]].
    apply (p4_constrained_ftu t r q s phi Hbnd w x HwC HxC); auto.
  - intros T HTunf _ [Hcov _].
    set (u := mkInst (fd x) (fqB x) (fz0 x) (fWp x) (fWm x) (fXp x) (fXm x) (fYp x) (fYm x) (fZ x) (negb (fp x))).
    assert (HuC : C_p4 t r q u = true).
    { unfold C_p4 in HxC |- *.
      change (fd u) with (fd x). change (fqB u) with (fqB x).
      change (is_phi t r q u) with (is_phi t r q x).
      rewrite Exd in HxC |- *.
      apply Bool.andb_true_iff in HxC. destruct HxC as [HqB _].
      rewrite HqB, Exphi, Bool.orb_true_r. reflexivity. }
    assert (HuS : agrees_on t r q s u x S_all_N).
    { repeat split; unfold u; simpl; intros; try reflexivity; discriminate. }
    pose proof (Hcov u HuC HuS) as HuT.
    destruct HuT as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hup]]]]]]]]]].
    pose proof (Hup HTunf) as Hfp. unfold u in Hfp; simpl in Hfp.
    exact (Bool.no_fixpoint_negb (fp x) Hfp).
Qed.

(* Case 2: fd x = false /\ is_phi t r q x = false (so is_dummy t r q x = true) *)
Definition S_dummy : Sub :=
  mkSub true false false
        (fun _ => false) (fun _ => false)
        (fun i => i =? 0) (fun i => i =? 0)
        (fun _ => false) (fun _ => false)
        (fun _ => false) false.

Lemma case_d0_dummy : forall t r q s phi x,
  1 <= r ->
  C_p4 t r q x = true ->
  fd x = false ->
  is_phi t r q x = false ->
  dec_exist_fair_at t r q s phi x.
Proof.
  intros t r q s phi x Hr HxC Exd Exphi.
  assert (Hxdummy : is_dummy t r q x = true).
  { unfold C_p4 in HxC. rewrite Exd, Exphi, Bool.orb_false_r in HxC.
    apply Bool.andb_true_iff in HxC. exact (proj2 HxC). }
  assert (Hxfp : fp x = false).
  { unfold is_dummy in Hxdummy.
    repeat (apply Bool.andb_true_iff in Hxdummy; destruct Hxdummy as [Hxdummy _]).
    destruct (fp x); [discriminate | reflexivity]. }
  assert (HxAB : all_X_true r x = true).
  { unfold is_dummy in Hxdummy.
    apply Bool.andb_true_iff in Hxdummy. destruct Hxdummy as [H1 _].
    apply Bool.andb_true_iff in H1. exact (proj2 H1). }
  assert (HxA0 : fXp x 0 = true /\ fXm x 0 = true).
  { pose proof (forall_nat_elim r _ HxAB 0 ltac:(lia)) as H0. simpl in H0.
    apply Bool.andb_true_iff in H0. exact H0. }
  destruct HxA0 as [HxA0 HxB0].
  assert (Hxk : kappa_p4 t r q phi x = false).
  { unfold kappa_p4. rewrite Exd, Exphi. reflexivity. }
  exists S_dummy. split; [reflexivity|]. split.
  - intros w HwC [Hd [_ [_ [_ [_ [HA [HB _]]]]]]].
    rewrite Hxk. unfold kappa_p4. rewrite (Hd eq_refl), Exd.
    destruct (is_phi t r q w) eqn:Ewphi; [|reflexivity]. exfalso.
    unfold is_phi in Ewphi. apply Bool.andb_true_iff in Ewphi. destruct Ewphi as [Ew1 _].
    apply Bool.andb_true_iff in Ew1. destruct Ew1 as [_ Hwxu].
    pose proof (forall_nat_elim r _ Hwxu 0 ltac:(lia)) as H0. simpl in H0.
    rewrite (HA 0 ltac:(lia) eq_refl), (HB 0 ltac:(lia) eq_refl), HxA0, HxB0 in H0. discriminate.
  - intros T HTunf HTw [Hcov [v [HvC [HvT HvnS]]]].
    assert (HTz0 : sz0 T = false).
    { destruct (sz0 T) eqn:Ez0; [|reflexivity]. exfalso.
      set (u := mkInst (fd x) (fqB x) (negb (fz0 x)) (fWp x) (fWm x) (fXp x) (fXm x) (fYp x) (fYm x) (fZ x) (fp x)).
      assert (HuC : C_p4 t r q u = true) by (unfold u; rewrite C_p4_flip_z0; exact HxC).
      assert (HuS : agrees_on t r q s u x S_dummy) by (repeat split; unfold u, S_dummy; simpl; intros; try reflexivity; discriminate).
      destruct (Hcov u HuC HuS) as [_ [_ [Huz0 _]]].
      pose proof (Huz0 Ez0) as Hfix. unfold u in Hfix; simpl in Hfix.
      exact (Bool.no_fixpoint_negb (fz0 x) Hfix). }
    assert (Hvfp : fp v = false).
    { destruct HvT as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hvp]]]]]]]]]].
      rewrite (Hvp HTunf). exact Hxfp. }
    assert (Hvfd : fd v = false).
    { destruct (fd v) eqn:Evd; [|reflexivity]. exfalso.
      unfold C_p4 in HvC. rewrite Evd, Hvfp in HvC. discriminate. }
    assert (Hvdummy : is_dummy t r q v = false).
    { destruct (is_dummy t r q v) eqn:Ed; [|reflexivity]. exfalso.
      apply HvnS.
      unfold is_dummy in Ed.
      apply Bool.andb_true_iff in Ed. destruct Ed as [Ed1 _].
      apply Bool.andb_true_iff in Ed1. destruct Ed1 as [_ HvAB].
      pose proof (forall_nat_elim r _ HvAB 0 ltac:(lia)) as H0. simpl in H0.
      apply Bool.andb_true_iff in H0. destruct H0 as [HvA0 HvB0].
      repeat split; unfold S_dummy; simpl; intros; try discriminate.
      - rewrite Hvfd, Exd. reflexivity.
      - apply Nat.eqb_eq in H0; subst i. rewrite HvA0, HxA0. reflexivity.
      - apply Nat.eqb_eq in H0; subst i. rewrite HvB0, HxB0. reflexivity. }
    assert (Hvphi : is_phi t r q v = true).
    { unfold C_p4 in HvC. rewrite Hvfd, Hvdummy, Bool.orb_false_l in HvC.
      apply Bool.andb_true_iff in HvC. exact (proj2 HvC). }
    set (v0 := mkInst (fd v) (fqB v) false (fWp v) (fWm v) (fXp v) (fXm v) (fYp v) (fYm v) (fZ v) (fp v)).
    assert (Hv0C : C_p4 t r q v0 = true) by (unfold v0; rewrite C_p4_set_z0_false; exact HvC).
    assert (Hv0T : agrees_on t r q s v0 x T).
    { destruct HvT as [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 H11]]]]]]]]]].
      repeat split; unfold v0; simpl; intros; auto.
      rewrite HTz0 in H; discriminate. }
    pose proof (HTw v0 Hv0C Hv0T) as Hkv0.
    rewrite Hxk in Hkv0.
    unfold kappa_p4 in Hkv0.
    change (fd v0) with (fd v) in Hkv0.
    change (fz0 v0) with false in Hkv0.
    change (is_phi t r q v0) with (is_phi t r q v) in Hkv0.
    rewrite Hvfd, Hvphi in Hkv0. discriminate.
Qed.

(* Helper Lemma: Any unfair weak AXp at x (with fp x = true, kappa x = false, sz0 T = false)
   forces fd v = true on all v in cov_T(x). *)
Lemma unfair_weak_axp_kappa0_p1_forces_d1 : forall t r q s phi x T v,
  fp x = true ->
  kappa_p4 t r q phi x = false ->
  is_unfair_P4 T ->
  weak_axp t r q s phi x T ->
  sz0 T = false ->
  C_p4 t r q v = true ->
  agrees_on t r q s v x T ->
  fd v = true.
Proof.
  intros t r q s phi x T v Hxfp Hxk HTunf HTw HTz0 HvC HvT.
  destruct (fd v) eqn:Evd; [reflexivity|]. exfalso.
  assert (Hvfp : fp v = true).
  { destruct HvT as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hvp]]]]]]]]]].
    rewrite (Hvp HTunf). exact Hxfp. }
  assert (Hvdummy : is_dummy t r q v = false).
  { unfold is_dummy. rewrite Hvfp. reflexivity. }
  assert (Hvphi : is_phi t r q v = true).
  { unfold C_p4 in HvC. rewrite Evd, Hvdummy, Bool.orb_false_l in HvC.
    apply Bool.andb_true_iff in HvC. exact (proj2 HvC). }
  set (v0 := mkInst (fd v) (fqB v) false (fWp v) (fWm v) (fXp v) (fXm v) (fYp v) (fYm v) (fZ v) (fp v)).
  assert (Hv0C : C_p4 t r q v0 = true) by (unfold v0; rewrite C_p4_set_z0_false; exact HvC).
  assert (Hv0T : agrees_on t r q s v0 x T).
  { destruct HvT as [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 H11]]]]]]]]]].
    repeat split; unfold v0; simpl; intros; auto.
    rewrite HTz0 in H; discriminate. }
  pose proof (HTw v0 Hv0C Hv0T) as Hkv0.
  rewrite Hxk in Hkv0.
  unfold kappa_p4 in Hkv0.
  change (fd v0) with (fd v) in Hkv0.
  change (fz0 v0) with false in Hkv0.
  change (is_phi t r q v0) with (is_phi t r q v) in Hkv0.
  rewrite Evd, Hvphi in Hkv0. discriminate.
Qed.

(* Case 3a: fd x = true /\ w_ok t x = false *)
Definition S_w0 (k0 : nat) : Sub :=
  mkSub false false false
        (fun k => k =? k0) (fun k => k =? k0)
        (fun _ => false) (fun _ => false)
        (fun _ => false) (fun _ => false)
        (fun _ => false) false.

Lemma case_d1_w_not_ok : forall t r q s phi x,
  C_p4 t r q x = true ->
  fd x = true ->
  w_ok t x = false ->
  dec_exist_fair_at t r q s phi x.
Proof.
  intros t r q s phi x HxC Exd Exwok.
  destruct (forall_nat_false_exists t _ Exwok) as [k0 [Hk0 Hk0false]].
  simpl in Hk0false. apply Bool.orb_false_iff in Hk0false.
  destruct Hk0false as [HxWA0 HxWB0].
  assert (Hxk : kappa_p4 t r q phi x = false).
  { unfold kappa_p4. rewrite Exd, Exwok. reflexivity. }
  exists (S_w0 k0). split; [reflexivity|]. split.
  - intros w HwC [_ [_ [_ [HWA [HWB _]]]]].
    rewrite Hxk.
    assert (HwWA0 : fWp w k0 = false).
    { rewrite (HWA k0 Hk0 (Nat.eqb_refl k0)). exact HxWA0. }
    assert (HwWB0 : fWm w k0 = false).
    { rewrite (HWB k0 Hk0 (Nat.eqb_refl k0)). exact HxWB0. }
    assert (Hwwok : w_ok t w = false).
    { destruct (w_ok t w) eqn:Ew; [|reflexivity]. exfalso.
      pose proof (forall_nat_elim t _ Ew k0 Hk0) as H0. simpl in H0.
      rewrite HwWA0, HwWB0 in H0. discriminate. }
    unfold kappa_p4. destruct (fd w).
    + rewrite Hwwok. reflexivity.
    + destruct (is_phi t r q w) eqn:Ephi; [|reflexivity]. exfalso.
      unfold is_phi in Ephi.
      apply Bool.andb_true_iff in Ephi. destruct Ephi as [Ephi1 _].
      apply Bool.andb_true_iff in Ephi1. destruct Ephi1 as [Hwu _].
      pose proof (w_uniq_implies_w_ok t w Hwu) as Hwok'. rewrite Hwwok in Hwok'. discriminate.
  - intros T HTunf HTw [Hcov [v [HvC [HvT HvnS]]]].
    assert (Hnotboth : sWp T k0 = false \/ sWm T k0 = false).
    { destruct (sWp T k0) eqn:EWA; [|left; reflexivity].
      destruct (sWm T k0) eqn:EWB; [|right; reflexivity].
      exfalso. apply HvnS.
      destruct HvT as [_ [_ [_ [HvWA [HvWB _]]]]].
      repeat split; unfold S_w0; simpl; intros; try discriminate.
      - apply Nat.eqb_eq in H0; subst k. apply (HvWA k0 Hk0 EWA).
      - apply Nat.eqb_eq in H0; subst k. apply (HvWB k0 Hk0 EWB). }
    destruct Hnotboth as [EsWA0 | EsWB0].
    + set (u_base := mkInst true false (fz0 x)
                            (fun k => if k =? k0 then false else true)
                            (fun _ => false)
                            (fun _ => true) (fun _ => true)
                            (fun _ => true) (fun _ => true)
                            (fZ x) true).
      assert (Hubwok : w_ok t u_base = false).
      { destruct (w_ok t u_base) eqn:Ew; [|reflexivity]. exfalso.
        pose proof (forall_nat_elim t _ Ew k0 Hk0) as H0. unfold u_base in H0; simpl in H0.
        rewrite Nat.eqb_refl in H0. discriminate. }
      assert (HubC : C_p4 t r q u_base = true).
      { unfold C_p4. simpl. rewrite Hubwok. simpl.
        apply Bool.andb_true_iff. split; [apply forall_nat_true; intros; reflexivity | reflexivity]. }
      assert (HubS : agrees_on t r q s u_base x (S_w0 k0)).
      { repeat split; unfold u_base, S_w0; simpl; intros; try discriminate.
        - rewrite H0. apply Nat.eqb_eq in H0; subst k. symmetry; exact HxWA0.
        - apply Nat.eqb_eq in H0; subst k. symmetry; exact HxWB0. }
      pose proof (Hcov u_base HubC HubS) as HubT.
      set (w_hit := mkInst true false (fz0 x)
                           (fun _ => true) (fun _ => false)
                           (fun _ => true) (fun _ => true)
                           (fun _ => true) (fun _ => true)
                           (fZ x) true).
      assert (Hwhwok : w_ok t w_hit = true) by (apply forall_nat_true; intros; reflexivity).
      assert (Hwhxok : x_ok r w_hit = true) by (apply forall_nat_true; intros; reflexivity).
      assert (Hwhwu : w_uniq t w_hit = true) by (apply forall_nat_true; intros; reflexivity).
      assert (HwhAB : all_X_true r w_hit = true) by (apply forall_nat_true; intros; reflexivity).
      assert (HwhY : all_Y_true q w_hit = true) by (apply forall_nat_true; intros; reflexivity).
      assert (HwhC : C_p4 t r q w_hit = true).
      { unfold C_p4. change (fd w_hit) with true. change (fp w_hit) with true. change (fqB w_hit) with false.
        rewrite HwhY, Hwhwok, Hwhxok, Hwhwu, HwhAB. reflexivity. }
      assert (HwhT : agrees_on t r q s w_hit x T).
      { destruct HubT as [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 H11]]]]]]]]]].
        repeat split; unfold w_hit; simpl; intros;
        try (exact (H1 H)); try (exact (H2 H)); try (exact (H3 H)); try (exact (H11 H));
        try (exact (H5 k H H0)); try (exact (H6 i H H0)); try (exact (H7 i H H0));
        try (exact (H8 j H H0)); try (exact (H9 j H H0)); try (exact (H10 m H H0)).
        pose proof (H4 k H H0) as Hk4. unfold u_base in Hk4; simpl in Hk4.
        destruct (Nat.eqb_spec k k0); [subst k; rewrite EsWA0 in H0; discriminate | exact Hk4]. }
      pose proof (HTw w_hit HwhC HwhT) as Hkwh.
      rewrite Hxk in Hkwh.
      unfold kappa_p4 in Hkwh. change (fd w_hit) with true in Hkwh.
      rewrite Hwhwok, Hwhxok in Hkwh. discriminate.
    + set (u_base := mkInst true false (fz0 x)
                            (fun _ => false)
                            (fun k => if k =? k0 then false else true)
                            (fun _ => true) (fun _ => true)
                            (fun _ => true) (fun _ => true)
                            (fZ x) true).
      assert (Hubwok : w_ok t u_base = false).
      { destruct (w_ok t u_base) eqn:Ew; [|reflexivity]. exfalso.
        pose proof (forall_nat_elim t _ Ew k0 Hk0) as H0. unfold u_base in H0; simpl in H0.
        rewrite Nat.eqb_refl in H0. discriminate. }
      assert (HubC : C_p4 t r q u_base = true).
      { unfold C_p4. simpl. rewrite Hubwok. simpl.
        apply Bool.andb_true_iff. split; [apply forall_nat_true; intros; reflexivity | reflexivity]. }
      assert (HubS : agrees_on t r q s u_base x (S_w0 k0)).
      { repeat split; unfold u_base, S_w0; simpl; intros; try discriminate.
        - apply Nat.eqb_eq in H0; subst k. symmetry; exact HxWA0.
        - rewrite H0. apply Nat.eqb_eq in H0; subst k. symmetry; exact HxWB0. }
      pose proof (Hcov u_base HubC HubS) as HubT.
      set (w_hit := mkInst true false (fz0 x)
                           (fun _ => false) (fun _ => true)
                           (fun _ => true) (fun _ => true)
                           (fun _ => true) (fun _ => true)
                           (fZ x) true).
      assert (Hwhwok : w_ok t w_hit = true) by (apply forall_nat_true; intros; reflexivity).
      assert (Hwhxok : x_ok r w_hit = true) by (apply forall_nat_true; intros; reflexivity).
      assert (Hwhwu : w_uniq t w_hit = true) by (apply forall_nat_true; intros; reflexivity).
      assert (HwhAB : all_X_true r w_hit = true) by (apply forall_nat_true; intros; reflexivity).
      assert (HwhY : all_Y_true q w_hit = true) by (apply forall_nat_true; intros; reflexivity).
      assert (HwhC : C_p4 t r q w_hit = true).
      { unfold C_p4. change (fd w_hit) with true. change (fp w_hit) with true. change (fqB w_hit) with false.
        rewrite HwhY, Hwhwok, Hwhxok, Hwhwu, HwhAB. reflexivity. }
      assert (HwhT : agrees_on t r q s w_hit x T).
      { destruct HubT as [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 H11]]]]]]]]]].
        repeat split; unfold w_hit; simpl; intros;
        try (exact (H1 H)); try (exact (H2 H)); try (exact (H3 H)); try (exact (H11 H));
        try (exact (H4 k H H0)); try (exact (H6 i H H0)); try (exact (H7 i H H0));
        try (exact (H8 j H H0)); try (exact (H9 j H H0)); try (exact (H10 m H H0)).
        pose proof (H5 k H H0) as Hk5. unfold u_base in Hk5; simpl in Hk5.
        destruct (Nat.eqb_spec k k0); [subst k; rewrite EsWB0 in H0; discriminate | exact Hk5]. }
      pose proof (HTw w_hit HwhC HwhT) as Hkwh.
      rewrite Hxk in Hkwh.
      unfold kappa_p4 in Hkwh. change (fd w_hit) with true in Hkwh.
      rewrite Hwhwok, Hwhxok in Hkwh. discriminate.
Qed.

(* Case 3b: fd x = true /\ w_ok t x = true /\ x_ok r x = false *)
Definition S_x0 (i0 : nat) : Sub :=
  mkSub true true false
        (fun _ => false) (fun _ => false)
        (fun i => i =? i0) (fun _ => false)
        (fun _ => false) (fun _ => false)
        (fun _ => false) false.

Lemma case_d1_x_not_ok : forall t r q s phi x,
  1 <= t ->
  C_p4 t r q x = true ->
  fd x = true ->
  w_ok t x = true ->
  x_ok r x = false ->
  dec_exist_fair_at t r q s phi x.
Proof.
  intros t r q s phi x Ht HxC Exd Exwok Exxok.
  destruct (forall_nat_false_exists r _ Exxok) as [i0 [Hi0 Hi0false]].
  simpl in Hi0false. apply Bool.orb_false_iff in Hi0false.
  destruct Hi0false as [HxA0 HxB0].
  assert (Hxk : kappa_p4 t r q phi x = false).
  { unfold kappa_p4. rewrite Exd, Exwok, Exxok. reflexivity. }
  assert (Hxfp : fp x = true).
  { unfold C_p4 in HxC. rewrite Exd in HxC.
    apply Bool.andb_true_iff in HxC. destruct HxC as [H1 _].
    apply Bool.andb_true_iff in H1. exact (proj1 H1). }
  assert (HxfqB : fqB x = false).
  { unfold C_p4 in HxC. rewrite Exd, Exwok, Exxok in HxC. simpl in HxC.
    apply Bool.andb_true_iff in HxC. destruct HxC as [_ HqB].
    destruct (fqB x); [discriminate | reflexivity]. }
  exists (S_x0 i0). split; [reflexivity|]. split.
  - intros w HwC [Hd [HqB [_ [_ [_ [HA _]]]]]].
    rewrite Hxk.
    assert (Hwd : fd w = true) by (rewrite (Hd eq_refl); exact Exd).
    assert (HwqB : fqB w = false) by (rewrite (HqB eq_refl); exact HxfqB).
    assert (HwA0 : fXp w i0 = false) by (rewrite (HA i0 Hi0 (Nat.eqb_refl i0)); exact HxA0).
    assert (HwAB : all_X_true r w = false).
    { destruct (all_X_true r w) eqn:EAB; [|reflexivity]. exfalso.
      pose proof (forall_nat_elim r _ EAB i0 Hi0) as H0. simpl in H0.
      rewrite HwA0 in H0. discriminate. }
    unfold kappa_p4. rewrite Hwd.
    destruct (w_ok t w && x_ok r w) eqn:Ewx; [|reflexivity]. exfalso.
    unfold C_p4 in HwC. rewrite Hwd, Ewx, HwAB, Bool.andb_false_r, HwqB, Bool.andb_false_r in HwC.
    discriminate.
  - intros T HTunf HTw [Hcov [v [HvC [HvT HvnS]]]].
    assert (HTz0 : sz0 T = false).
    { destruct (sz0 T) eqn:Ez0; [|reflexivity]. exfalso.
      set (u := mkInst (fd x) (fqB x) (negb (fz0 x)) (fWp x) (fWm x) (fXp x) (fXm x) (fYp x) (fYm x) (fZ x) (fp x)).
      assert (HuC : C_p4 t r q u = true) by (unfold u; rewrite C_p4_flip_z0; exact HxC).
      assert (HuS : agrees_on t r q s u x (S_x0 i0)) by (repeat split; unfold u, S_x0; simpl; intros; try reflexivity; discriminate).
      destruct (Hcov u HuC HuS) as [_ [_ [Huz0 _]]].
      pose proof (Huz0 Ez0) as Hfix. unfold u in Hfix; simpl in Hfix.
      exact (Bool.no_fixpoint_negb (fz0 x) Hfix). }
    assert (Hvfd : fd v = true).
    { exact (unfair_weak_axp_kappa0_p1_forces_d1 t r q s phi x T v Hxfp Hxk HTunf HTw HTz0 HvC HvT). }
    assert (Hnotboth : sqB T = false \/ sXp T i0 = false).
    { destruct (sqB T) eqn:EqB; [|left; reflexivity].
      destruct (sXp T i0) eqn:EA0; [|right; reflexivity].
      exfalso. apply HvnS.
      destruct HvT as [_ [HvqB [_ [_ [_ [HvA _]]]]]].
      repeat split; unfold S_x0; simpl; intros; try discriminate.
      - rewrite Hvfd, Exd. reflexivity.
      - exact (HvqB EqB).
      - apply Nat.eqb_eq in H0; subst i. exact (HvA i0 Hi0 EA0). }
    set (u_base_A := mkInst true false (fz0 x)
                            (fun _ => true) (fun _ => false)
                            (fun i => if i =? i0 then false else true)
                            (fun i => if i =? i0 then false else true)
                            (fun _ => true) (fun _ => true)
                            (fZ x) true).
    assert (HubAxok : x_ok r u_base_A = false).
    { destruct (x_ok r u_base_A) eqn:Ex; [|reflexivity]. exfalso.
      pose proof (forall_nat_elim r _ Ex i0 Hi0) as H0. unfold u_base_A in H0; simpl in H0.
      rewrite Nat.eqb_refl in H0. discriminate. }
    assert (HubAC : C_p4 t r q u_base_A = true).
    { unfold C_p4. change (fd u_base_A) with true. change (fp u_base_A) with true. change (fqB u_base_A) with false.
      rewrite HubAxok, Bool.andb_false_r. simpl.
      apply Bool.andb_true_iff. split; [apply forall_nat_true; intros; reflexivity | reflexivity]. }
    assert (HubAS : agrees_on t r q s u_base_A x (S_x0 i0)).
    { repeat split; unfold u_base_A, S_x0; simpl; intros; try discriminate.
      - symmetry; exact Exd.
      - symmetry; exact HxfqB.
      - rewrite H0. apply Nat.eqb_eq in H0; subst i. symmetry; exact HxA0. }
    pose proof (Hcov u_base_A HubAC HubAS) as HubAT.
    set (u_base_B := mkInst true false (fz0 x)
                            (fun _ => false) (fun _ => false)
                            (fun i => if i =? i0 then false else true)
                            (fun _ => true)
                            (fun _ => true) (fun _ => true)
                            (fZ x) true).
    assert (HubBwok : w_ok t u_base_B = false).
    { destruct (w_ok t u_base_B) eqn:Ew; [|reflexivity]. exfalso.
      pose proof (forall_nat_elim t _ Ew 0 ltac:(lia)) as H0. unfold u_base_B in H0; simpl in H0.
      discriminate. }
    assert (HubBC : C_p4 t r q u_base_B = true).
    { unfold C_p4. change (fd u_base_B) with true. change (fp u_base_B) with true. change (fqB u_base_B) with false.
      rewrite HubBwok. simpl.
      apply Bool.andb_true_iff. split; [apply forall_nat_true; intros; reflexivity | reflexivity]. }
    assert (HubBS : agrees_on t r q s u_base_B x (S_x0 i0)).
    { repeat split; unfold u_base_B, S_x0; simpl; intros; try discriminate.
      - symmetry; exact Exd.
      - symmetry; exact HxfqB.
      - rewrite H0. apply Nat.eqb_eq in H0; subst i. symmetry; exact HxA0. }
    pose proof (Hcov u_base_B HubBC HubBS) as HubBT.
    destruct Hnotboth as [EsqB | EsA0].
    + set (w_hit := mkInst true true (fz0 x)
                           (fun _ => true) (fun _ => false)
                           (fun i => if i =? i0 then false else true)
                           (fun _ => true)
                           (fun _ => true) (fun _ => true)
                           (fZ x) true).
      assert (Hwhwok : w_ok t w_hit = true) by (apply forall_nat_true; intros; reflexivity).
      assert (Hwhxok : x_ok r w_hit = true) by (apply forall_nat_true; intros; apply Bool.orb_true_r).
      assert (HwhAB : all_X_true r w_hit = false).
      { destruct (all_X_true r w_hit) eqn:EAB; [|reflexivity]. exfalso.
        pose proof (forall_nat_elim r _ EAB i0 Hi0) as H0. unfold w_hit in H0; simpl in H0.
        rewrite Nat.eqb_refl in H0. discriminate. }
      assert (HwhY : all_Y_true q w_hit = true) by (apply forall_nat_true; intros; reflexivity).
      assert (HwhC : C_p4 t r q w_hit = true).
      { unfold C_p4. change (fd w_hit) with true. change (fp w_hit) with true. change (fqB w_hit) with true.
        rewrite HwhY, Hwhwok, Hwhxok, HwhAB, Bool.andb_false_r. reflexivity. }
      assert (HwhT : agrees_on t r q s w_hit x T).
      { destruct HubAT as [HA1 [HA2 [HA3 [HA4 [HA5 [HA6 [HA7 [HA8 [HA9 [HA10 HA11]]]]]]]]]].
        destruct HubBT as [_ [_ [_ [_ [_ [_ [HB7 _]]]]]]].
        repeat split; unfold w_hit; simpl; intros;
        try (exact (HA1 H)); try (exact (HA3 H)); try (exact (HA11 H));
        try (exact (HA4 k H H0)); try (exact (HA5 k H H0)); try (exact (HA6 i H H0));
        try (exact (HB7 i H H0)); try (exact (HA8 j H H0)); try (exact (HA9 j H H0));
        try (exact (HA10 m H H0)).
        rewrite EsqB in H; discriminate. }
      pose proof (HTw w_hit HwhC HwhT) as Hkwh.
      rewrite Hxk in Hkwh.
      unfold kappa_p4 in Hkwh. change (fd w_hit) with true in Hkwh.
      rewrite Hwhwok, Hwhxok in Hkwh. discriminate.
    + set (w_hit := mkInst true false (fz0 x)
                           (fun _ => true) (fun _ => false)
                           (fun _ => true) (fun _ => true)
                           (fun _ => true) (fun _ => true)
                           (fZ x) true).
      assert (Hwhwok : w_ok t w_hit = true) by (apply forall_nat_true; intros; reflexivity).
      assert (Hwhxok : x_ok r w_hit = true) by (apply forall_nat_true; intros; reflexivity).
      assert (Hwhwu : w_uniq t w_hit = true) by (apply forall_nat_true; intros; reflexivity).
      assert (HwhAB : all_X_true r w_hit = true) by (apply forall_nat_true; intros; reflexivity).
      assert (HwhY : all_Y_true q w_hit = true) by (apply forall_nat_true; intros; reflexivity).
      assert (HwhC : C_p4 t r q w_hit = true).
      { unfold C_p4. change (fd w_hit) with true. change (fp w_hit) with true. change (fqB w_hit) with false.
        rewrite HwhY, Hwhwok, Hwhxok, Hwhwu, HwhAB. reflexivity. }
      assert (HwhT : agrees_on t r q s w_hit x T).
      { destruct HubAT as [HA1 [HA2 [HA3 [HA4 [HA5 [HA6 [HA7 [HA8 [HA9 [HA10 HA11]]]]]]]]]].
        destruct HubBT as [_ [_ [_ [_ [_ [_ [HB7 _]]]]]]].
        repeat split; unfold w_hit; simpl; intros;
        try (exact (HA1 H)); try (exact (HA2 H)); try (exact (HA3 H)); try (exact (HA11 H));
        try (exact (HA4 k H H0)); try (exact (HA5 k H H0));
        try (exact (HB7 i H H0)); try (exact (HA8 j H H0)); try (exact (HA9 j H H0));
        try (exact (HA10 m H H0)).
        pose proof (HA6 i H H0) as Hi6. unfold u_base_A in Hi6; simpl in Hi6.
        destruct (Nat.eqb_spec i i0); [subst i; rewrite EsA0 in H0; discriminate | exact Hi6]. }
      pose proof (HTw w_hit HwhC HwhT) as Hkwh.
      rewrite Hxk in Hkwh.
      unfold kappa_p4 in Hkwh. change (fd w_hit) with true in Hkwh.
      rewrite Hwhwok, Hwhxok in Hkwh. discriminate.
Qed.

(* Case 4: fd x = true /\ w_ok t x && x_ok r x = true /\ w_uniq t x && all_X_true r x = false *)
Definition S_qB : Sub :=
  mkSub false true false
        (fun _ => false) (fun _ => false)
        (fun _ => false) (fun _ => false)
        (fun _ => false) (fun _ => false)
        (fun _ => false) false.

Lemma case_d1_qB1 : forall t r q s phi x,
  1 <= t -> 1 <= r ->
  C_p4 t r q x = true ->
  fd x = true ->
  w_ok t x && x_ok r x = true ->
  w_uniq t x && all_X_true r x = false ->
  dec_exist_fair_at t r q s phi x.
Proof.
  intros t r q s phi x Ht Hr HxC Exd Exwx ExwuAB.
  assert (HxfqB : fqB x = true).
  { unfold C_p4 in HxC. rewrite Exd, Exwx, ExwuAB in HxC.
    apply Bool.andb_true_iff in HxC. exact (proj2 HxC). }
  assert (Hxk : kappa_p4 t r q phi x = true).
  { unfold kappa_p4. rewrite Exd, Exwx. reflexivity. }
  exists S_qB. split; [reflexivity|]. split.
  - intros w HwC [_ [HqB _]].
    rewrite Hxk.
    assert (HwqB : fqB w = true) by (rewrite (HqB eq_refl); exact HxfqB).
    unfold C_p4 in HwC.
    destruct (fd w) eqn:Ewd.
    + unfold kappa_p4. rewrite Ewd.
      destruct (w_ok t w && x_ok r w); [reflexivity|].
      rewrite HwqB, Bool.andb_false_r in HwC. discriminate.
    + rewrite HwqB in HwC. discriminate.
  - intros T _ HTw [Hcov [v [HvC [HvT HvnS]]]].
    assert (EsqB : sqB T = false).
    { destruct (sqB T) eqn:EqB; [|reflexivity]. exfalso.
      apply HvnS. destruct HvT as [_ [HvqB _]].
      repeat split; unfold S_qB; simpl; intros; try discriminate.
      exact (HvqB EqB). }
    assert (EsWA0 : sWp T 0 = false).
    { destruct (sWp T 0) eqn:EWA0; [|reflexivity]. exfalso.
      set (u1 := mkInst true true (fz0 x)
                        (fun k => if k =? 0 then negb (fWp x 0) else true)
                        (fun _ => true)
                        (fun i => if i =? 0 then false else true)
                        (fun _ => true)
                        (fun _ => true) (fun _ => true)
                        (fZ x) true).
      assert (Hu1wok : w_ok t u1 = true) by (apply forall_nat_true; intros; apply Bool.orb_true_r).
      assert (Hu1xok : x_ok r u1 = true) by (apply forall_nat_true; intros; apply Bool.orb_true_r).
      assert (Hu1AB : all_X_true r u1 = false).
      { destruct (all_X_true r u1) eqn:EAB; [|reflexivity]. exfalso.
        pose proof (forall_nat_elim r _ EAB 0 ltac:(lia)) as H0. unfold u1 in H0; simpl in H0. discriminate. }
      assert (Hu1Y : all_Y_true q u1 = true) by (apply forall_nat_true; intros; reflexivity).
      assert (Hu1C : C_p4 t r q u1 = true).
      { unfold C_p4. change (fd u1) with true. change (fp u1) with true. change (fqB u1) with true.
        rewrite Hu1Y, Hu1wok, Hu1xok, Hu1AB, Bool.andb_false_r. reflexivity. }
      assert (Hu1S : agrees_on t r q s u1 x S_qB).
      { repeat split; unfold u1, S_qB; simpl; intros; try discriminate. symmetry; exact HxfqB. }
      destruct (Hcov u1 Hu1C Hu1S) as [_ [_ [_ [Hu1WA _]]]].
      pose proof (Hu1WA 0 ltac:(lia) EWA0) as Hfix. unfold u1 in Hfix; simpl in Hfix.
      exact (Bool.no_fixpoint_negb (fWp x 0) Hfix). }
    assert (EsWB0 : sWm T 0 = false).
    { destruct (sWm T 0) eqn:EWB0; [|reflexivity]. exfalso.
      set (u2 := mkInst true true (fz0 x)
                        (fun _ => true)
                        (fun k => if k =? 0 then negb (fWm x 0) else true)
                        (fun i => if i =? 0 then false else true)
                        (fun _ => true)
                        (fun _ => true) (fun _ => true)
                        (fZ x) true).
      assert (Hu2wok : w_ok t u2 = true) by (apply forall_nat_true; intros; reflexivity).
      assert (Hu2xok : x_ok r u2 = true) by (apply forall_nat_true; intros; apply Bool.orb_true_r).
      assert (Hu2AB : all_X_true r u2 = false).
      { destruct (all_X_true r u2) eqn:EAB; [|reflexivity]. exfalso.
        pose proof (forall_nat_elim r _ EAB 0 ltac:(lia)) as H0. unfold u2 in H0; simpl in H0. discriminate. }
      assert (Hu2Y : all_Y_true q u2 = true) by (apply forall_nat_true; intros; reflexivity).
      assert (Hu2C : C_p4 t r q u2 = true).
      { unfold C_p4. change (fd u2) with true. change (fp u2) with true. change (fqB u2) with true.
        rewrite Hu2Y, Hu2wok, Hu2xok, Hu2AB, Bool.andb_false_r. reflexivity. }
      assert (Hu2S : agrees_on t r q s u2 x S_qB).
      { repeat split; unfold u2, S_qB; simpl; intros; try discriminate. symmetry; exact HxfqB. }
      destruct (Hcov u2 Hu2C Hu2S) as [_ [_ [_ [_ [Hu2WB _]]]]].
      pose proof (Hu2WB 0 ltac:(lia) EWB0) as Hfix. unfold u2 in Hfix; simpl in Hfix.
      exact (Bool.no_fixpoint_negb (fWm x 0) Hfix). }
    set (w_bad := mkInst (fd x) false (fz0 x)
                         (fun k => if k =? 0 then false else fWp x k)
                         (fun k => if k =? 0 then false else fWm x k)
                         (fXp x) (fXm x) (fYp x) (fYm x) (fZ x) (fp x)).
    assert (Hwbwok : w_ok t w_bad = false).
    { destruct (w_ok t w_bad) eqn:Ew; [|reflexivity]. exfalso.
      pose proof (forall_nat_elim t _ Ew 0 ltac:(lia)) as H0. unfold w_bad in H0; simpl in H0. discriminate. }
    assert (HwbC : C_p4 t r q w_bad = true).
    { unfold C_p4 in HxC |- *.
      change (fd w_bad) with (fd x). change (fp w_bad) with (fp x).
      change (fqB w_bad) with false.
      change (all_Y_true q w_bad) with (all_Y_true q x).
      rewrite Exd in HxC |- *.
      apply Bool.andb_true_iff in HxC. destruct HxC as [Hx1 _].
      rewrite Hx1, Hwbwok. reflexivity. }
    assert (HwbT : agrees_on t r q s w_bad x T).
    { repeat split; unfold w_bad; simpl; intros; try reflexivity.
      - rewrite EsqB in H; discriminate.
      - destruct (Nat.eqb_spec k 0); [subst k; rewrite EsWA0 in H0; discriminate | reflexivity].
      - destruct (Nat.eqb_spec k 0); [subst k; rewrite EsWB0 in H0; discriminate | reflexivity]. }
    pose proof (HTw w_bad HwbC HwbT) as Hkwb.
    rewrite Hxk in Hkwb.
    unfold kappa_p4 in Hkwb. change (fd w_bad) with (fd x) in Hkwb.
    rewrite Exd, Hwbwok in Hkwb. discriminate.
Qed.

(* Case 5: fd x = true /\ w_ok t x && x_ok r x = true /\ w_uniq t x && all_X_true r x = true *)
Definition S_of_WX (x : Inst) (X : nat -> bool) : Sub :=
  mkSub true false false
        (fWp x) (fWm x)
        X (fun i => negb (X i))
        (fun _ => false) (fun _ => false)
        (fun _ => false) false.

Definition inst_d0_phi (W X Y Z : nat -> bool) : Inst :=
  mkInst false false true
         W (fun k => negb (W k))
         X (fun i => negb (X i))
         Y (fun j => negb (Y j))
         Z true.

Lemma is_phi_inst_d0_phi : forall t r q W X Y Z,
  is_phi t r q (inst_d0_phi W X Y Z) = true.
Proof.
  intros t r q W X Y Z. unfold is_phi, inst_d0_phi.
  repeat (apply Bool.andb_true_iff; split);
  apply forall_nat_true; intros; simpl.
  - destruct (W i); reflexivity.
  - destruct (X i); reflexivity.
  - destruct (Y i); reflexivity.
Qed.

Lemma C_p4_inst_d0_phi : forall t r q W X Y Z,
  C_p4 t r q (inst_d0_phi W X Y Z) = true.
Proof.
  intros t r q W X Y Z. unfold C_p4. change (fd (inst_d0_phi W X Y Z)) with false.
  change (fqB (inst_d0_phi W X Y Z)) with false.
  rewrite is_phi_inst_d0_phi, Bool.orb_true_r. reflexivity.
Qed.

Lemma kappa_p4_inst_d0_phi : forall t r q phi W X Y Z,
  kappa_p4 t r q phi (inst_d0_phi W X Y Z) =
  negb (eval_cnf (combine4 t r q W X Y Z) phi).
Proof.
  intros t r q phi W X Y Z. unfold kappa_p4.
  change (fd (inst_d0_phi W X Y Z)) with false.
  change (fz0 (inst_d0_phi W X Y Z)) with true.
  rewrite is_phi_inst_d0_phi. reflexivity.
Qed.

Lemma case_d1_target_W : forall t r q s phi x,
  1 <= t -> 1 <= r ->
  cnf_bounded (t + r + q + s) phi ->
  four_qbf t r q phi ->
  C_p4 t r q x = true ->
  fd x = true ->
  w_ok t x && x_ok r x = true ->
  w_uniq t x && all_X_true r x = true ->
  dec_exist_fair_at t r q s phi x.
Proof.
  intros t r q s phi x Ht Hr Hbnd Hqbf HxC Exd Exwx ExwuAB.
  apply Bool.andb_true_iff in Exwx. destruct Exwx as [Exwok Exxok].
  apply Bool.andb_true_iff in ExwuAB. destruct ExwuAB as [Exwu ExAB].
  assert (Hxfp : fp x = true).
  { unfold C_p4 in HxC. rewrite Exd in HxC.
    apply Bool.andb_true_iff in HxC. destruct HxC as [H1 _].
    apply Bool.andb_true_iff in H1. exact (proj1 H1). }
  assert (HxY : all_Y_true q x = true).
  { unfold C_p4 in HxC. rewrite Exd in HxC.
    apply Bool.andb_true_iff in HxC. destruct HxC as [H1 _].
    apply Bool.andb_true_iff in H1. exact (proj2 H1). }
  assert (Hxk : kappa_p4 t r q phi x = true).
  { unfold kappa_p4. rewrite Exd, Exwok, Exxok. reflexivity. }
  assert (HxWB_eq : forall k, k < t -> fWm x k = negb (fWp x k)).
  { intros k Hk. pose proof (forall_nat_elim t _ Exwu k Hk) as H0. simpl in H0.
    destruct (fWp x k); destruct (fWm x k); simpl in *; try discriminate; reflexivity. }
  assert (HxA_true : forall i, i < r -> fXp x i = true).
  { intros i Hi. pose proof (forall_nat_elim r _ ExAB i Hi) as H0. simpl in H0.
    apply Bool.andb_true_iff in H0. exact (proj1 H0). }
  assert (HxB_true : forall i, i < r -> fXm x i = true).
  { intros i Hi. pose proof (forall_nat_elim r _ ExAB i Hi) as H0. simpl in H0.
    apply Bool.andb_true_iff in H0. exact (proj2 H0). }
  assert (HxY_true : forall j, j < q -> fYp x j = true /\ fYm x j = true).
  { intros j Hj. pose proof (forall_nat_elim q _ HxY j Hj) as H0. simpl in H0.
    apply Bool.andb_true_iff in H0. exact H0. }
  destruct (Hqbf (fWp x)) as [X HX].
  exists (S_of_WX x X). split; [reflexivity|]. split.
  - intros w HwC [Hd [_ [_ [HWA [HWB [HA [HB _]]]]]]].
    rewrite Hxk. unfold kappa_p4. rewrite (Hd eq_refl), Exd.
    apply Bool.andb_true_iff. split.
    + unfold w_ok. apply forall_nat_true. intros k Hk.
      destruct (fWp x k) eqn:EWA.
      * rewrite (HWA k Hk EWA), EWA. reflexivity.
      * assert (EWB : fWm x k = true) by (rewrite (HxWB_eq k Hk), EWA; reflexivity).
        rewrite (HWB k Hk EWB), EWB, Bool.orb_true_r. reflexivity.
    + unfold x_ok. apply forall_nat_true. intros i Hi.
      destruct (X i) eqn:EX.
      * rewrite (HA i Hi EX), (HxA_true i Hi). reflexivity.
      * assert (EXb : negb (X i) = true) by (rewrite EX; reflexivity).
        rewrite (HB i Hi EXb), (HxB_true i Hi), Bool.orb_true_r. reflexivity.
  - intros T HTunf HTw [Hcov [v [HvC [HvT HvnS]]]].
    (* Witness 1 in cov_S(x): u_all1 proves sqB=false, sz0=false, sZ=false, and sWp/sWm alignment *)
    set (u_all1 := mkInst true true (negb (fz0 x))
                          (fun _ => true) (fun _ => true)
                          (fun _ => true) (fun _ => true)
                          (fun _ => true) (fun _ => true)
                          (fun m => negb (fZ x m)) true).
    assert (Hu1wok : w_ok t u_all1 = true) by (apply forall_nat_true; intros; reflexivity).
    assert (Hu1xok : x_ok r u_all1 = true) by (apply forall_nat_true; intros; reflexivity).
    assert (Hu1wu : w_uniq t u_all1 = false).
    { destruct (w_uniq t u_all1) eqn:Ewu; [|reflexivity]. exfalso.
      pose proof (forall_nat_elim t _ Ewu 0 ltac:(lia)) as H0. unfold u_all1 in H0; simpl in H0. discriminate. }
    assert (Hu1Y : all_Y_true q u_all1 = true) by (apply forall_nat_true; intros; reflexivity).
    assert (Hu1C : C_p4 t r q u_all1 = true).
    { unfold C_p4. change (fd u_all1) with true. change (fp u_all1) with true. change (fqB u_all1) with true.
      rewrite Hu1Y, Hu1wok, Hu1xok, Hu1wu. reflexivity. }
    assert (Hu1S : agrees_on t r q s u_all1 x (S_of_WX x X)).
    { repeat split; unfold u_all1, S_of_WX; simpl; intros; try discriminate.
      - symmetry; exact Exd.
      - symmetry; exact H0.
      - symmetry; exact H0.
      - symmetry; exact (HxA_true i H).
      - symmetry; exact (HxB_true i H). }
    pose proof (Hcov u_all1 Hu1C Hu1S) as Hu1T.
    destruct Hu1T as [_ [Hu1qB [Hu1z0 [Hu1WA [Hu1WB [_ [_ [_ [_ [Hu1Z _]]]]]]]]]].
    assert (HxfqB : fqB x = false).
    { unfold C_p4 in HxC. rewrite Exd, Exwok, Exxok, Exwu, ExAB in HxC. simpl in HxC.
      apply Bool.andb_true_iff in HxC. destruct HxC as [_ HqB].
      destruct (fqB x); [discriminate | reflexivity]. }
    assert (HTqB : sqB T = false).
    { destruct (sqB T) eqn:EqB; [|reflexivity].
      pose proof (Hu1qB eq_refl) as Hfix. unfold u_all1 in Hfix; simpl in Hfix.
      rewrite HxfqB in Hfix. discriminate. }
    assert (HTz0 : sz0 T = false).
    { destruct (sz0 T) eqn:Ez0; [|reflexivity]. exfalso.
      pose proof (Hu1z0 eq_refl) as Hfix. unfold u_all1 in Hfix; simpl in Hfix.
      exact (Bool.no_fixpoint_negb (fz0 x) Hfix). }
    assert (HTZ : forall m, m < s -> sZ T m = false).
    { intros m Hm. destruct (sZ T m) eqn:EZ; [|reflexivity]. exfalso.
      pose proof (Hu1Z m Hm EZ) as Hfix. unfold u_all1 in Hfix; simpl in Hfix.
      exact (Bool.no_fixpoint_negb (fZ x m) Hfix). }
    assert (HTWA : forall k, k < t -> sWp T k = true -> fWp x k = true).
    { intros k Hk HkWA. symmetry. exact (Hu1WA k Hk HkWA). }
    assert (HTWB : forall k, k < t -> sWm T k = true -> fWm x k = true).
    { intros k Hk HkWB. symmetry. exact (Hu1WB k Hk HkWB). }
    (* Witness 2 in cov_S(x): u_X proves sXp/sXm alignment with X *)
    set (u_X := mkInst true true (fz0 x)
                       (fWp x) (fWm x)
                       X (fun i => negb (X i))
                       (fun _ => true) (fun _ => true)
                       (fZ x) true).
    assert (HuXwok : w_ok t u_X = true) by exact Exwok.
    assert (HuXxok : x_ok r u_X = true).
    { unfold x_ok, u_X; simpl. apply forall_nat_true. intros i _. destruct (X i); reflexivity. }
    assert (HuXAB : all_X_true r u_X = false).
    { destruct (all_X_true r u_X) eqn:EAB; [|reflexivity]. exfalso.
      pose proof (forall_nat_elim r _ EAB 0 ltac:(lia)) as H0. unfold u_X in H0; simpl in H0.
      destruct (X 0); discriminate. }
    assert (HuXY : all_Y_true q u_X = true) by (apply forall_nat_true; intros; reflexivity).
    assert (HuXC : C_p4 t r q u_X = true).
    { unfold C_p4. change (fd u_X) with true. change (fp u_X) with true. change (fqB u_X) with true.
      rewrite HuXY, HuXwok, HuXxok, HuXAB, Bool.andb_false_r. reflexivity. }
    assert (HuXS : agrees_on t r q s u_X x (S_of_WX x X)).
    { repeat split; unfold u_X, S_of_WX; simpl; intros; try reflexivity; try discriminate.
      - symmetry; exact Exd.
      - rewrite H0, (HxA_true i H). reflexivity.
      - rewrite H0, (HxB_true i H). reflexivity. }
    pose proof (Hcov u_X HuXC HuXS) as HuXT.
    destruct HuXT as [_ [_ [_ [_ [_ [HuXA [HuXB _]]]]]]].
    assert (HTA : forall i, i < r -> sXp T i = true -> X i = true).
    { intros i Hi HiA. pose proof (HuXA i Hi HiA) as Hfix. unfold u_X in Hfix; simpl in Hfix.
      rewrite (HxA_true i Hi) in Hfix. exact Hfix. }
    assert (HTB : forall i, i < r -> sXm T i = true -> X i = false).
    { intros i Hi HiB. pose proof (HuXB i Hi HiB) as Hfix. unfold u_X in Hfix; simpl in Hfix.
      rewrite (HxB_true i Hi) in Hfix.
      destruct (X i); [discriminate | reflexivity]. }
    (* Check if T forces fd = true (either sd T = true or exists j < q, sYp T j = true /\ sYm T j = true) *)
    destruct (classic (sd T = true \/ exists j, j < q /\ sYp T j = true /\ sYm T j = true)) as [Hforces_d1 | Hreaches_d0].
    + assert (Hvfd : fd v = true).
      { destruct HvT as [Hvd [_ [_ [_ [_ [_ [_ [HvY [HvYb [_ Hvp]]]]]]]]]].
        destruct Hforces_d1 as [Esd | [j0 [Hj0 [EY1 EYb1]]]].
        - rewrite (Hvd Esd). exact Exd.
        - destruct (fd v) eqn:Evd; [reflexivity|]. exfalso.
          assert (Hvfp : fp v = true) by (rewrite (Hvp HTunf); exact Hxfp).
          assert (Hvdummy : is_dummy t r q v = false) by (unfold is_dummy; rewrite Hvfp; reflexivity).
          assert (Hvphi : is_phi t r q v = false).
          { destruct (is_phi t r q v) eqn:Ephi; [|reflexivity]. exfalso.
            unfold is_phi in Ephi. apply Bool.andb_true_iff in Ephi. destruct Ephi as [_ Hvyu].
            pose proof (forall_nat_elim q _ Hvyu j0 Hj0) as H0. simpl in H0.
            destruct (HxY_true j0 Hj0) as [HxY0 HxYb0].
            rewrite (HvY j0 Hj0 EY1), (HvYb j0 Hj0 EYb1), HxY0, HxYb0 in H0. discriminate. }
          unfold C_p4 in HvC. rewrite Evd, Hvdummy, Hvphi, Bool.andb_false_r in HvC. discriminate. }
      assert (HTW_cover : forall k, k < t -> sWp T k = true \/ sWm T k = true).
      { intros k Hk.
        destruct (sWp T k) eqn:EWA; [left; reflexivity|].
        destruct (sWm T k) eqn:EWB; [right; reflexivity|].
        exfalso.
        set (w_w0 := mkInst true false (fz0 x)
                            (fun m => if m =? k then false else fWp x m)
                            (fun m => if m =? k then false else fWm x m)
                            (fXp x) (fXm x) (fYp x) (fYm x) (fZ x) true).
        assert (Hwwok : w_ok t w_w0 = false).
        { destruct (w_ok t w_w0) eqn:Ew; [|reflexivity]. exfalso.
          pose proof (forall_nat_elim t _ Ew k Hk) as H0. unfold w_w0 in H0; simpl in H0.
          rewrite Nat.eqb_refl in H0. discriminate. }
        assert (HwC : C_p4 t r q w_w0 = true).
        { unfold C_p4. change (fd w_w0) with true. change (fp w_w0) with true. change (fqB w_w0) with false.
          change (all_Y_true q w_w0) with (all_Y_true q x).
          rewrite HxY, Hwwok. reflexivity. }
        assert (HwT : agrees_on t r q s w_w0 x T).
        { repeat split; unfold w_w0; simpl; intros; try reflexivity;
          try (symmetry; exact Exd); try (symmetry; exact HxfqB); try (symmetry; exact Hxfp).
          - destruct (Nat.eqb_spec k0 k); [subst k0; rewrite EWA in H0; discriminate | reflexivity].
          - destruct (Nat.eqb_spec k0 k); [subst k0; rewrite EWB in H0; discriminate | reflexivity]. }
        pose proof (HTw w_w0 HwC HwT) as Hkw.
        rewrite Hxk in Hkw.
        unfold kappa_p4 in Hkw. change (fd w_w0) with true in Hkw.
        rewrite Hwwok in Hkw. discriminate. }
      assert (HTX_cover : forall i, i < r -> sXp T i = true \/ sXm T i = true).
      { intros i Hi.
        destruct (sXp T i) eqn:EA; [left; reflexivity|].
        destruct (sXm T i) eqn:EB; [right; reflexivity|].
        exfalso.
        set (w_x0 := mkInst true false (fz0 x)
                            (fWp x) (fWm x)
                            (fun m => if m =? i then false else fXp x m)
                            (fun m => if m =? i then false else fXm x m)
                            (fYp x) (fYm x) (fZ x) true).
        assert (Hwxok : x_ok r w_x0 = false).
        { destruct (x_ok r w_x0) eqn:Ex; [|reflexivity]. exfalso.
          pose proof (forall_nat_elim r _ Ex i Hi) as H0. unfold w_x0 in H0; simpl in H0.
          rewrite Nat.eqb_refl in H0. discriminate. }
        assert (HwC : C_p4 t r q w_x0 = true).
        { unfold C_p4. change (fd w_x0) with true. change (fp w_x0) with true. change (fqB w_x0) with false.
          change (all_Y_true q w_x0) with (all_Y_true q x).
          rewrite HxY, Hwxok, Bool.andb_false_r. reflexivity. }
        assert (HwT : agrees_on t r q s w_x0 x T).
        { repeat split; unfold w_x0; simpl; intros; try reflexivity;
          try (symmetry; exact Exd); try (symmetry; exact HxfqB); try (symmetry; exact Hxfp).
          - destruct (Nat.eqb_spec i0 i); [subst i0; rewrite EA in H0; discriminate | reflexivity].
          - destruct (Nat.eqb_spec i0 i); [subst i0; rewrite EB in H0; discriminate | reflexivity]. }
        pose proof (HTw w_x0 HwC HwT) as Hkw.
        rewrite Hxk in Hkw.
        unfold kappa_p4 in Hkw. change (fd w_x0) with true in Hkw.
        rewrite Hwxok, Bool.andb_false_r in Hkw. discriminate. }
      apply HvnS.
      destruct HvT as [_ [_ [_ [HvWA [HvWB [HvA [HvB _]]]]]]].
      repeat split; unfold S_of_WX; simpl; intros; try discriminate.
      * rewrite Hvfd, Exd. reflexivity.
      * destruct (HTW_cover k H) as [EWA | EWB].
        -- exact (HvWA k H EWA).
        -- pose proof (HTWB k H EWB) as HWBk. rewrite (HxWB_eq k H), H0 in HWBk. discriminate.
      * destruct (HTW_cover k H) as [EWA | EWB].
        -- pose proof (HTWA k H EWA) as HWAk. rewrite (HxWB_eq k H), HWAk in H0. discriminate.
        -- exact (HvWB k H EWB).
      * destruct (HTX_cover i H) as [EA | EB].
        -- exact (HvA i H EA).
        -- pose proof (HTB i H EB) as HBi. rewrite H0 in HBi. discriminate.
      * destruct (HTX_cover i H) as [EA | EB].
        -- pose proof (HTA i H EA) as HAi. rewrite HAi in H0. discriminate.
        -- exact (HvB i H EB).
    + apply not_or_and in Hreaches_d0. destruct Hreaches_d0 as [HTd_not1 HTnoYboth].
      assert (HTsd : sd T = false) by (destruct (sd T); [contradiction | reflexivity]).
      set (Y := fun j => negb (sYm T j)).
      destruct (HX Y) as [Z HZ].
      set (w_phi := inst_d0_phi (fWp x) X Y Z).
      assert (HwC : C_p4 t r q w_phi = true) by apply C_p4_inst_d0_phi.
      assert (HwT : agrees_on t r q s w_phi x T).
      { repeat split; unfold w_phi, inst_d0_phi; simpl; intros.
        - rewrite HTsd in H; discriminate.
        - rewrite HTqB in H; discriminate.
        - rewrite HTz0 in H; discriminate.
        - symmetry; exact (HxWB_eq k H).
        - rewrite (HTA i H H0), (HxA_true i H). reflexivity.
        - rewrite (HTB i H H0), (HxB_true i H). reflexivity.
        - unfold Y. destruct (sYm T j) eqn:EYb.
          + exfalso. apply HTnoYboth. exists j; auto.
          + symmetry; exact (proj1 (HxY_true j H)).
        - unfold Y. rewrite Bool.negb_involutive, H0.
          symmetry; exact (proj2 (HxY_true j H)).
        - rewrite (HTZ m H) in H0; discriminate.
        - symmetry; exact Hxfp. }
      pose proof (HTw w_phi HwC HwT) as Hkw.
      unfold w_phi in Hkw. rewrite kappa_p4_inst_d0_phi, HZ, Hxk in Hkw. discriminate.
Qed.

Theorem four_qbf_implies_cls_exist_fair : forall t r q s phi,
  1 <= t -> 1 <= r ->
  cnf_bounded (t + r + q + s) phi ->
  four_qbf t r q phi ->
  cls_exist_fair t r q s phi.
Proof.
  intros t r q s phi Ht Hr Hbnd Hqbf x HxC.
    destruct (fd x) eqn:Exd.
    + destruct (w_ok t x) eqn:Exwok.
      * destruct (x_ok r x) eqn:Exxok.
        -- assert (Exwx : w_ok t x && x_ok r x = true) by (rewrite Exwok, Exxok; reflexivity).
           destruct (w_uniq t x && all_X_true r x) eqn:ExwuAB.
           ++ exact (case_d1_target_W t r q s phi x Ht Hr Hbnd Hqbf HxC Exd Exwx ExwuAB).
           ++ exact (case_d1_qB1 t r q s phi x Ht Hr HxC Exd Exwx ExwuAB).
        -- exact (case_d1_x_not_ok t r q s phi x Ht HxC Exd Exwok Exxok).
      * exact (case_d1_w_not_ok t r q s phi x HxC Exd Exwok).
    + destruct (is_phi t r q x) eqn:Exphi.
      * exact (case_d0_phi t r q s phi x Hbnd HxC Exd Exphi).
      * exact (case_d0_dummy t r q s phi x Hr HxC Exd Exphi).
Qed.

(* ========================================================================= *)
(* Direction 2: cls_exist_fair -> four_qbf                                   *)
(* ========================================================================= *)

Definition inst_target_W (W : nat -> bool) : Inst :=
  mkInst true false true
         W (fun k => negb (W k))
         (fun _ => true) (fun _ => true)
         (fun _ => true) (fun _ => true)
         (fun _ => true) true.

Definition inst_dummy_W (W : nat -> bool) : Inst :=
  mkInst false false true
         W (fun k => negb (W k))
         (fun _ => true) (fun _ => true)
         (fun _ => true) (fun _ => true)
         (fun _ => true) false.

Lemma w_uniq_target_W : forall t W, w_uniq t (inst_target_W W) = true.
Proof.
  intros t W. unfold w_uniq, inst_target_W; simpl.
  apply forall_nat_true. intros k _. destruct (W k); reflexivity.
Qed.

Lemma w_ok_target_W : forall t W, w_ok t (inst_target_W W) = true.
Proof.
  intros t W. apply w_uniq_implies_w_ok. apply w_uniq_target_W.
Qed.

Lemma C_p4_target_W : forall t r q W, C_p4 t r q (inst_target_W W) = true.
Proof.
  intros t r q W. unfold C_p4.
  change (fd (inst_target_W W)) with true.
  change (fp (inst_target_W W)) with true.
  change (fqB (inst_target_W W)) with false.
  rewrite w_ok_target_W, w_uniq_target_W.
  assert (Hxok : x_ok r (inst_target_W W) = true) by (apply forall_nat_true; intros; reflexivity).
  assert (HAB : all_X_true r (inst_target_W W) = true) by (apply forall_nat_true; intros; reflexivity).
  assert (HY : all_Y_true q (inst_target_W W) = true) by (apply forall_nat_true; intros; reflexivity).
  rewrite Hxok, HAB, HY. reflexivity.
Qed.

Lemma kappa_p4_target_W : forall t r q phi W,
  kappa_p4 t r q phi (inst_target_W W) = true.
Proof.
  intros t r q phi W. unfold kappa_p4.
  change (fd (inst_target_W W)) with true.
  rewrite w_ok_target_W.
  assert (Hxok : x_ok r (inst_target_W W) = true) by (apply forall_nat_true; intros; reflexivity).
  rewrite Hxok. reflexivity.
Qed.

Lemma C_p4_dummy_W : forall t r q W, C_p4 t r q (inst_dummy_W W) = true.
Proof.
  intros t r q W. unfold C_p4.
  change (fd (inst_dummy_W W)) with false.
  change (fqB (inst_dummy_W W)) with false.
  assert (Hdummy : is_dummy t r q (inst_dummy_W W) = true).
  { unfold is_dummy. change (fp (inst_dummy_W W)) with false.
    change (w_ok t (inst_dummy_W W)) with (w_ok t (inst_target_W W)).
    rewrite w_ok_target_W.
    repeat (apply Bool.andb_true_iff; split); try reflexivity;
    apply forall_nat_true; intros; reflexivity. }
  rewrite Hdummy. reflexivity.
Qed.

Lemma kappa_p4_dummy_W : forall t r q phi W,
  1 <= r ->
  kappa_p4 t r q phi (inst_dummy_W W) = false.
Proof.
  intros t r q phi W Hr. unfold kappa_p4.
  change (fd (inst_dummy_W W)) with false.
  assert (Hphi : is_phi t r q (inst_dummy_W W) = false).
  { destruct (is_phi t r q (inst_dummy_W W)) eqn:Ephi; [|reflexivity]. exfalso.
    unfold is_phi in Ephi.
    apply Bool.andb_true_iff in Ephi. destruct Ephi as [Ephi1 _].
    apply Bool.andb_true_iff in Ephi1. destruct Ephi1 as [_ Hxu].
    pose proof (forall_nat_elim r _ Hxu 0 ltac:(lia)) as H0.
    unfold inst_dummy_W in H0; simpl in H0. discriminate. }
  rewrite Hphi. reflexivity.
Qed.

Theorem cls_exist_fair_implies_four_qbf : forall t r q s phi,
  1 <= r ->
  cnf_bounded (t + r + q + s) phi ->
  cls_exist_fair t r q s phi ->
  four_qbf t r q phi.
Proof.
  intros t r q s phi Hr Hbnd Hexist W.
  destruct (Hexist (inst_target_W W) (C_p4_target_W t r q W)) as [S [HSfair [HSw HSno]]].
  assert (HSd : sd S = true).
  { destruct (sd S) eqn:Ed; [reflexivity|]. exfalso.
    assert (Hag : agrees_on t r q s (inst_dummy_W W) (inst_target_W W) S).
    { repeat split; unfold inst_dummy_W, inst_target_W; simpl; intros; try reflexivity.
      - rewrite Ed in H; discriminate.
      - rewrite HSfair in H; discriminate. }
    pose proof (HSw (inst_dummy_W W) (C_p4_dummy_W t r q W) Hag) as Hkd.
    rewrite (kappa_p4_dummy_W t r q phi W Hr), kappa_p4_target_W in Hkd. discriminate. }
  assert (HSW : forall k, k < t -> (W k = true -> sWp S k = true) /\ (W k = false -> sWm S k = true)).
  { intros k Hk. split; intro HWk.
    - destruct (sWp S k) eqn:EWA; [reflexivity|]. exfalso.
      set (w := mkInst true false true
                       (fun m => if m =? k then false else W m)
                       (fun m => negb (W m))
                       (fun _ => true) (fun _ => true)
                       (fun _ => true) (fun _ => true)
                       (fun _ => true) true).
      assert (Hwwok : w_ok t w = false).
      { destruct (w_ok t w) eqn:Ew; [|reflexivity]. exfalso.
        pose proof (forall_nat_elim t _ Ew k Hk) as H0. unfold w in H0; simpl in H0.
        rewrite Nat.eqb_refl, HWk in H0. discriminate. }
      assert (HwC : C_p4 t r q w = true).
      { unfold C_p4. change (fd w) with true. change (fp w) with true. change (fqB w) with false.
        rewrite Hwwok. simpl.
        apply Bool.andb_true_iff. split; [apply forall_nat_true; intros; reflexivity | reflexivity]. }
      assert (HwS : agrees_on t r q s w (inst_target_W W) S).
      { repeat split; unfold w, inst_target_W; simpl; intros; try reflexivity.
        destruct (Nat.eqb_spec k0 k); [subst k0; rewrite EWA in H0; discriminate | reflexivity]. }
      pose proof (HSw w HwC HwS) as Hkw.
      rewrite kappa_p4_target_W in Hkw.
      unfold kappa_p4 in Hkw. change (fd w) with true in Hkw.
      rewrite Hwwok in Hkw. discriminate.
    - destruct (sWm S k) eqn:EWB; [reflexivity|]. exfalso.
      set (w := mkInst true false true
                       W
                       (fun m => if m =? k then false else negb (W m))
                       (fun _ => true) (fun _ => true)
                       (fun _ => true) (fun _ => true)
                       (fun _ => true) true).
      assert (Hwwok : w_ok t w = false).
      { destruct (w_ok t w) eqn:Ew; [|reflexivity]. exfalso.
        pose proof (forall_nat_elim t _ Ew k Hk) as H0. unfold w in H0; simpl in H0.
        rewrite Nat.eqb_refl, HWk in H0. discriminate. }
      assert (HwC : C_p4 t r q w = true).
      { unfold C_p4. change (fd w) with true. change (fp w) with true. change (fqB w) with false.
        rewrite Hwwok. simpl.
        apply Bool.andb_true_iff. split; [apply forall_nat_true; intros; reflexivity | reflexivity]. }
      assert (HwS : agrees_on t r q s w (inst_target_W W) S).
      { repeat split; unfold w, inst_target_W; simpl; intros; try reflexivity.
        destruct (Nat.eqb_spec k0 k); [subst k0; rewrite EWB in H0; discriminate | reflexivity]. }
      pose proof (HSw w HwC HwS) as Hkw.
      rewrite kappa_p4_target_W in Hkw.
      unfold kappa_p4 in Hkw. change (fd w) with true in Hkw.
      rewrite Hwwok in Hkw. discriminate. }
  assert (HSAB : forall i, i < r -> sXp S i = true \/ sXm S i = true).
  { intros i Hi.
    destruct (sXp S i) eqn:EA; [left; reflexivity|].
    destruct (sXm S i) eqn:EB; [right; reflexivity|].
    exfalso.
    set (w := mkInst true false true
                     W (fun m => negb (W m))
                     (fun m => if m =? i then false else true)
                     (fun m => if m =? i then false else true)
                     (fun _ => true) (fun _ => true)
                     (fun _ => true) true).
    assert (Hwxok : x_ok r w = false).
    { destruct (x_ok r w) eqn:Ex; [|reflexivity]. exfalso.
      pose proof (forall_nat_elim r _ Ex i Hi) as H0. unfold w in H0; simpl in H0.
      rewrite Nat.eqb_refl in H0. discriminate. }
    assert (HwC : C_p4 t r q w = true).
    { unfold C_p4. change (fd w) with true. change (fp w) with true. change (fqB w) with false.
      rewrite Hwxok, Bool.andb_false_r. simpl.
      apply Bool.andb_true_iff. split; [apply forall_nat_true; intros; reflexivity | reflexivity]. }
    assert (HwS : agrees_on t r q s w (inst_target_W W) S).
    { repeat split; unfold w, inst_target_W; simpl; intros; try reflexivity.
      - destruct (Nat.eqb_spec i0 i); [subst i0; rewrite EA in H0; discriminate | reflexivity].
      - destruct (Nat.eqb_spec i0 i); [subst i0; rewrite EB in H0; discriminate | reflexivity]. }
    pose proof (HSw w HwC HwS) as Hkw.
    rewrite kappa_p4_target_W in Hkw.
    unfold kappa_p4 in Hkw. change (fd w) with true in Hkw.
    rewrite Hwxok, Bool.andb_false_r in Hkw. discriminate. }
  set (X := fun i => sXp S i).
  exists X. intro Y.
  destruct (classic (exists Z : nat -> bool, eval_cnf (combine4 t r q W X Y Z) phi = true)) as [Hok | HnoZ]; [exact Hok|].
  exfalso.
  assert (HallZ : forall Z : nat -> bool, eval_cnf (combine4 t r q W X Y Z) phi = false).
  { intro Z. destruct (eval_cnf (combine4 t r q W X Y Z) phi) eqn:E; [|reflexivity].
    exfalso. apply HnoZ. exists Z; exact E. }
  set (T := mkSub false false false
                  W (fun k => negb (W k))
                  X (fun i => negb (X i))
                  Y (fun j => negb (Y j))
                  (fun _ => false) true).
  apply (HSno T eq_refl).
  - intros w HwC [Hd [_ [_ [HWA [HWB [HA [HB [HY [HYb [_ Hp]]]]]]]]]].
    rewrite kappa_p4_target_W.
    destruct (fd w) eqn:Ewd.
    + unfold kappa_p4. rewrite Ewd. apply Bool.andb_true_iff. split.
      * unfold w_ok. apply forall_nat_true. intros k Hk.
        destruct (W k) eqn:EWk.
        -- rewrite (HWA k Hk EWk); simpl; rewrite EWk; reflexivity.
        -- assert (EWkb : negb (W k) = true) by (rewrite EWk; reflexivity).
           rewrite (HWB k Hk EWkb); simpl; rewrite EWkb, Bool.orb_true_r; reflexivity.
      * unfold x_ok. apply forall_nat_true. intros i Hi.
        destruct (X i) eqn:EXi.
        -- rewrite (HA i Hi EXi); reflexivity.
        -- assert (EXib : negb (X i) = true) by (rewrite EXi; reflexivity).
           rewrite (HB i Hi EXib), Bool.orb_true_r; reflexivity.
    + assert (Hwfp : fp w = true) by (exact (Hp eq_refl)).
      assert (Hwdummy : is_dummy t r q w = false) by (unfold is_dummy; rewrite Hwfp; reflexivity).
      assert (Hwphi : is_phi t r q w = true).
      { unfold C_p4 in HwC. rewrite Ewd, Hwdummy, Bool.orb_false_l in HwC.
        apply Bool.andb_true_iff in HwC. exact (proj2 HwC). }
      unfold kappa_p4. rewrite Ewd, Hwphi.
      destruct (fz0 w) eqn:Ewz0; [|reflexivity].
      unfold is_phi in Hwphi.
      apply Bool.andb_true_iff in Hwphi. destruct Hwphi as [Hwphi1 Hwyu].
      apply Bool.andb_true_iff in Hwphi1. destruct Hwphi1 as [Hwwu Hwxu].
      assert (HextW : forall k, k < t -> fWp w k = W k).
      { intros k Hk. destruct (W k) eqn:EWk.
        - rewrite (HWA k Hk EWk); simpl; exact EWk.
        - assert (EWkb : negb (W k) = true) by (rewrite EWk; reflexivity).
          pose proof ( HWB k Hk EWkb) as HWBk; simpl in HWBk. rewrite EWkb in HWBk.
          pose proof (forall_nat_elim t _ Hwwu k Hk) as H0; simpl in H0.
          rewrite HWBk in H0. destruct (fWp w k); [discriminate | reflexivity]. }
      assert (HextX : forall i, i < r -> fXp w i = X i).
      { intros i Hi. destruct (X i) eqn:EXi.
        - exact (HA i Hi EXi).
        - assert (EXib : negb (X i) = true) by (rewrite EXi; reflexivity).
          pose proof (HB i Hi EXib) as HBi; simpl in HBi.
          pose proof (forall_nat_elim r _ Hwxu i Hi) as H0; simpl in H0.
          rewrite HBi in H0. destruct (fXp w i); [discriminate | reflexivity]. }
      assert (HextY : forall j, j < q -> fYp w j = Y j).
      { intros j Hj. destruct (Y j) eqn:EYj.
        - exact (HY j Hj EYj).
        - assert (EYjb : negb (Y j) = true) by (rewrite EYj; reflexivity).
          pose proof (HYb j Hj EYjb) as HYbj; simpl in HYbj.
          pose proof (forall_nat_elim q _ Hwyu j Hj) as H0; simpl in H0.
          rewrite HYbj in H0. destruct (fYp w j); [discriminate | reflexivity]. }
      assert (Heval : eval_cnf (combine4 t r q (fWp w) (fXp w) (fYp w) (fZ w)) phi =
                      eval_cnf (combine4 t r q W X Y (fZ w)) phi).
      { apply (eval_cnf_ext_bounded (t + r + q + s) phi _ _ Hbnd).
        intros k Hk. apply (combine4_ext t r q s); auto. }
      rewrite Heval, (HallZ (fZ w)). reflexivity.
  - split.
    + intros u HuC [Hud [_ [_ [HuWA [HuWB [HuA [HuB _]]]]]]].
      assert (Hufd : fd u = true) by (exact (Hud HSd)).
      unfold C_p4 in HuC. rewrite Hufd in HuC.
      apply Bool.andb_true_iff in HuC. destruct HuC as [Hu1 _].
      apply Bool.andb_true_iff in Hu1. destruct Hu1 as [Hufp HuY].
      repeat split; unfold T, inst_target_W; simpl; intros; try discriminate.
      * exact (HuWA k H (proj1 (HSW k H) H0)).
      * destruct (W k) eqn:EWk; [discriminate | rewrite (HuWB k H (proj2 (HSW k H) EWk)); simpl; rewrite EWk; reflexivity].
      * exact (HuA i H H0).
      * destruct (HSAB i H) as [EA | EB].
        -- unfold X in H0; rewrite EA in H0; discriminate.
        -- exact (HuB i H EB).
      * pose proof (forall_nat_elim q _ HuY j H) as H1; simpl in H1.
        apply Bool.andb_true_iff in H1. exact (proj1 H1).
      * pose proof (forall_nat_elim q _ HuY j H) as H1; simpl in H1.
        apply Bool.andb_true_iff in H1. exact (proj2 H1).
      * exact Hufp.
    + set (v := inst_d0_phi W X Y (fun _ => true)).
      exists v. split; [apply C_p4_inst_d0_phi | split].
      * repeat split; unfold v, inst_d0_phi, T, inst_target_W; simpl; intros; try reflexivity; try discriminate; try exact H0.
      * intros [Hvd _]. pose proof (Hvd HSd) as Hbad. unfold v, inst_d0_phi, inst_target_W in Hbad; simpl in Hbad. discriminate.
Qed.

(* ========================================================================= *)
(* Literal Definition 3, 4, 15 Bridge: cls_exist_fair <-> cls_exist_fair_pi  *)
(* ========================================================================= *)

Lemma sub_le_trans : forall t r q s A B C,
  sub_le t r q s A B -> sub_le t r q s B C -> sub_le t r q s A C.
Proof.
  intros t r q s A B C
    [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 H11]]]]]]]]]]
    [G1 [G2 [G3 [G4 [G5 [G6 [G7 [G8 [G9 [G10 G11]]]]]]]]]].
  repeat split; intros; auto.
Qed.

Lemma agrees_sub_le : forall t r q s w x S1 S2,
  sub_le t r q s S1 S2 -> agrees_on t r q s w x S2 -> agrees_on t r q s w x S1.
Proof.
  intros t r q s w x S1 S2
    [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 H11]]]]]]]]]]
    [G1 [G2 [G3 [G4 [G5 [G6 [G7 [G8 [G9 [G10 G11]]]]]]]]]].
  repeat split; intros; auto.
Qed.

Fixpoint sum_bool (n : nat) (f : nat -> bool) : nat :=
  match n with
  | 0 => 0
  | S m => (if f m then 1 else 0) + sum_bool m f
  end.

Definition sub_weight (t r q s : nat) (S : Sub) : nat :=
  (if sd S then 1 else 0) + (if sqB S then 1 else 0) + (if sz0 S then 1 else 0) +
  sum_bool t (sWp S) + sum_bool t (sWm S) +
  sum_bool r (sXp S) + sum_bool r (sXm S) +
  sum_bool q (sYp S) + sum_bool q (sYm S) + sum_bool s (sZ S) +
  (if sp S then 1 else 0).

Lemma sum_bool_le : forall n f1 f2,
  (forall i, i < n -> f1 i = true -> f2 i = true) ->
  sum_bool n f1 <= sum_bool n f2.
Proof.
  induction n as [|m IH]; intros f1 f2 H; simpl; [lia|].
  assert (Hm : (if f1 m then 1 else 0) <= (if f2 m then 1 else 0)).
  { destruct (f1 m) eqn:E1; [rewrite (H m ltac:(lia) E1); lia | destruct (f2 m); lia]. }
  assert (Hr : sum_bool m f1 <= sum_bool m f2) by (apply IH; intros i Hi; apply H; lia).
  lia.
Qed.

Lemma sum_bool_lt : forall n f1 f2 i0,
  (forall i, i < n -> f1 i = true -> f2 i = true) ->
  i0 < n -> f2 i0 = true -> f1 i0 = false ->
  sum_bool n f1 < sum_bool n f2.
Proof.
  induction n as [|m IH]; intros f1 f2 i0 Hle Hi0 H2 H1; simpl; [lia|].
  destruct (Nat.eq_dec i0 m).
  - subst. rewrite H2, H1.
    assert (Hr : sum_bool m f1 <= sum_bool m f2) by (apply sum_bool_le; intros i Hi; apply Hle; lia).
    lia.
  - assert (Hm : (if f1 m then 1 else 0) <= (if f2 m then 1 else 0)).
    { destruct (f1 m) eqn:E1; [rewrite (Hle m ltac:(lia) E1); lia | destruct (f2 m); lia]. }
    assert (Hr : sum_bool m f1 < sum_bool m f2) by (apply (IH f1 f2 i0); [intros i Hi; apply Hle; lia | lia | exact H2 | exact H1]).
    lia.
Qed.

Lemma sub_weight_lt : forall t r q s S1 S2,
  sub_strict_lt t r q s S1 S2 -> sub_weight t r q s S1 < sub_weight t r q s S2.
Proof.
  intros t r q s S1 S2 [[H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 H11]]]]]]]]]] Hlt].
  unfold sub_weight.
  assert (W1 : (if sd S1 then 1 else 0) <= (if sd S2 then 1 else 0))
    by (destruct (sd S1) eqn:E; [rewrite (H1 eq_refl); lia | destruct (sd S2); lia]).
  assert (W2 : (if sqB S1 then 1 else 0) <= (if sqB S2 then 1 else 0))
    by (destruct (sqB S1) eqn:E; [rewrite (H2 eq_refl); lia | destruct (sqB S2); lia]).
  assert (W3 : (if sz0 S1 then 1 else 0) <= (if sz0 S2 then 1 else 0))
    by (destruct (sz0 S1) eqn:E; [rewrite (H3 eq_refl); lia | destruct (sz0 S2); lia]).
  assert (W4 : sum_bool t (sWp S1) <= sum_bool t (sWp S2)) by (apply sum_bool_le; exact H4).
  assert (W5 : sum_bool t (sWm S1) <= sum_bool t (sWm S2)) by (apply sum_bool_le; exact H5).
  assert (W6 : sum_bool r (sXp S1) <= sum_bool r (sXp S2)) by (apply sum_bool_le; exact H6).
  assert (W7 : sum_bool r (sXm S1) <= sum_bool r (sXm S2)) by (apply sum_bool_le; exact H7).
  assert (W8 : sum_bool q (sYp S1) <= sum_bool q (sYp S2)) by (apply sum_bool_le; exact H8).
  assert (W9 : sum_bool q (sYm S1) <= sum_bool q (sYm S2)) by (apply sum_bool_le; exact H9).
  assert (W10 : sum_bool s (sZ S1) <= sum_bool s (sZ S2)) by (apply sum_bool_le; exact H10).
  assert (W11 : (if sp S1 then 1 else 0) <= (if sp S2 then 1 else 0))
    by (destruct (sp S1) eqn:E; [rewrite (H11 eq_refl); lia | destruct (sp S2); lia]).
  destruct Hlt as [[Ha Hb] | [[Ha Hb] | [[Ha Hb] | [[k [Hk [Ha Hb]]] | [[k [Hk [Ha Hb]]] |
                 [[i [Hi [Ha Hb]]] | [[i [Hi [Ha Hb]]] | [[j [Hj [Ha Hb]]] | [[j [Hj [Ha Hb]]] |
                 [[m [Hm [Ha Hb]]] | [Ha Hb]]]]]]]]]]].
  - rewrite Ha, Hb in *; lia.
  - rewrite Ha, Hb in *; lia.
  - rewrite Ha, Hb in *; lia.
  - pose proof (sum_bool_lt t (sWp S1) (sWp S2) k H4 Hk Ha Hb); lia.
  - pose proof (sum_bool_lt t (sWm S1) (sWm S2) k H5 Hk Ha Hb); lia.
  - pose proof (sum_bool_lt r (sXp S1) (sXp S2) i H6 Hi Ha Hb); lia.
  - pose proof (sum_bool_lt r (sXm S1) (sXm S2) i H7 Hi Ha Hb); lia.
  - pose proof (sum_bool_lt q (sYp S1) (sYp S2) j H8 Hj Ha Hb); lia.
  - pose proof (sum_bool_lt q (sYm S1) (sYm S2) j H9 Hj Ha Hb); lia.
  - pose proof (sum_bool_lt s (sZ S1) (sZ S2) m H10 Hm Ha Hb); lia.
  - rewrite Ha, Hb in *; lia.
Qed.

Lemma weak_axp_has_axp : forall t r q s phi x S,
  weak_axp t r q s phi x S ->
  exists S' : Sub, sub_le t r q s S' S /\ is_axp t r q s phi x S'.
Proof.
  intros t r q s phi x S HS.
  remember (sub_weight t r q s S) as w eqn:Hw.
  revert S Hw HS.
  induction w as [w IH] using lt_wf_ind.
  intros S Hw HS.
  destruct (classic (is_axp t r q s phi x S)) as [Haxp | Hnot].
  - exists S. split; [repeat split; intros; auto | exact Haxp].
  - unfold is_axp in Hnot.
    apply not_and_or in Hnot. destruct Hnot as [Hbad | Hnotmin]; [contradiction|].
    apply not_all_ex_not in Hnotmin. destruct Hnotmin as [S1 HS1].
    apply imply_to_and in HS1. destruct HS1 as [Hlt Hnotweak].
    apply NNPP in Hnotweak.
    assert (Hw1 : sub_weight t r q s S1 < w) by (subst w; apply sub_weight_lt; exact Hlt).
    destruct (IH (sub_weight t r q s S1) Hw1 S1 eq_refl Hnotweak) as [S' [Hle' Haxp']].
    exists S'. split; [|exact Haxp'].
    apply (sub_le_trans t r q s S' S1 S Hle' (proj1 Hlt)).
Qed.

Fixpoint all_vecs (n : nat) : list (nat -> bool) :=
  match n with
  | 0 => [fun _ => false]
  | S m =>
      let rest := all_vecs m in
      map (fun f k => if k =? m then false else f k) rest ++
      map (fun f k => if k =? m then true else f k) rest
  end.

Lemma all_vecs_complete : forall n (f : nat -> bool),
  exists g, In g (all_vecs n) /\ forall k, k < n -> g k = f k.
Proof.
  induction n as [|m IH]; intro f; simpl.
  - exists (fun _ => false). split; [left; reflexivity | intros k Hk; lia].
  - destruct (IH f) as [g [Hg1 Hg2]].
    destruct (f m) eqn:Efm.
    + exists (fun k => if k =? m then true else g k). split.
      * apply in_or_app. right. exact (in_map (fun h k => if k =? m then true else h k) _ g Hg1).
      * intros k Hk. destruct (Nat.eqb_spec k m); [subst; symmetry; exact Efm | apply Hg2; lia].
    + exists (fun k => if k =? m then false else g k). split.
      * apply in_or_app. left. exact (in_map (fun h k => if k =? m then false else h k) _ g Hg1).
      * intros k Hk. destruct (Nat.eqb_spec k m); [subst; symmetry; exact Efm | apply Hg2; lia].
Qed.

Definition prod_list {A B : Type} (la : list A) (lb : list B) : list (A * B) :=
  flat_map (fun a => map (fun b => (a, b)) lb) la.

Lemma prod_list_in : forall {A B : Type} (la : list A) (lb : list B) a b,
  In a la -> In b lb -> In (a, b) (prod_list la lb).
Proof.
  intros A B la lb a b Ha Hb. unfold prod_list.
  apply in_flat_map. exists a. split; [exact Ha | apply in_map; exact Hb].
Qed.

Definition all_bools : list bool := [false; true].

Definition all_insts_p4 (t r q s : nat) : list Inst :=
  map (fun '(d, qB, z0, WA, WB, A, B, Y, Yb, Z, p) => mkInst d qB z0 WA WB A B Y Yb Z p)
      (prod_list
        (prod_list
          (prod_list
            (prod_list
              (prod_list
                (prod_list
                  (prod_list
                    (prod_list
                      (prod_list
                        (prod_list all_bools all_bools)
                        all_bools)
                      (all_vecs t))
                    (all_vecs t))
                  (all_vecs r))
                (all_vecs r))
              (all_vecs q))
            (all_vecs q))
          (all_vecs s))
        all_bools).

Definition same_inst_p4 (t r q s : nat) (u w : Inst) : Prop :=
  fd u = fd w /\
  fqB u = fqB w /\
  fz0 u = fz0 w /\
  (forall k, k < t -> fWp u k = fWp w k) /\
  (forall k, k < t -> fWm u k = fWm w k) /\
  (forall i, i < r -> fXp u i = fXp w i) /\
  (forall i, i < r -> fXm u i = fXm w i) /\
  (forall j, j < q -> fYp u j = fYp w j) /\
  (forall j, j < q -> fYm u j = fYm w j) /\
  (forall m, m < s -> fZ u m = fZ w m) /\
  fp u = fp w.

Lemma all_insts_p4_complete : forall t r q s w,
  exists u, In u (all_insts_p4 t r q s) /\ same_inst_p4 t r q s u w.
Proof.
  intros t r q s w.
  destruct (all_vecs_complete t (fWp w)) as [gWA [HgWA1 HgWA2]].
  destruct (all_vecs_complete t (fWm w)) as [gWB [HgWB1 HgWB2]].
  destruct (all_vecs_complete r (fXp w)) as [gA [HgA1 HgA2]].
  destruct (all_vecs_complete r (fXm w)) as [gB [HgB1 HgB2]].
  destruct (all_vecs_complete q (fYp w)) as [gY [HgY1 HgY2]].
  destruct (all_vecs_complete q (fYm w)) as [gYb [HgYb1 HgYb2]].
  destruct (all_vecs_complete s (fZ w)) as [gZ [HgZ1 HgZ2]].
  assert (Hd : In (fd w) all_bools) by (unfold all_bools; destruct (fd w); simpl; auto).
  assert (HqB : In (fqB w) all_bools) by (unfold all_bools; destruct (fqB w); simpl; auto).
  assert (Hz0 : In (fz0 w) all_bools) by (unfold all_bools; destruct (fz0 w); simpl; auto).
  assert (Hp : In (fp w) all_bools) by (unfold all_bools; destruct (fp w); simpl; auto).
  exists (mkInst (fd w) (fqB w) (fz0 w) gWA gWB gA gB gY gYb gZ (fp w)). split.
  - unfold all_insts_p4.
    change (mkInst (fd w) (fqB w) (fz0 w) gWA gWB gA gB gY gYb gZ (fp w)) with
      ((fun '(d, qB, z0, WA, WB, A, B, Y, Yb, Z, p) => mkInst d qB z0 WA WB A B Y Yb Z p)
         (fd w, fqB w, fz0 w, gWA, gWB, gA, gB, gY, gYb, gZ, fp w)).
    apply in_map. repeat apply prod_list_in; assumption.
  - repeat split; simpl; auto.
Qed.

Lemma C_p4_same_inst : forall t r q s u w,
  same_inst_p4 t r q s u w -> C_p4 t r q u = C_p4 t r q w.
Proof.
  intros t r q s u w [Hd [HqB [Hz0 [HWA [HWB [HA [HB [HY [HYb [_ Hp]]]]]]]]]].
  assert (Ewok : w_ok t u = w_ok t w) by (unfold w_ok; apply forall_nat_ext; intros k Hk; rewrite (HWA k Hk), (HWB k Hk); reflexivity).
  assert (Exok : x_ok r u = x_ok r w) by (unfold x_ok; apply forall_nat_ext; intros i Hi; rewrite (HA i Hi), (HB i Hi); reflexivity).
  assert (Ewu : w_uniq t u = w_uniq t w) by (unfold w_uniq; apply forall_nat_ext; intros k Hk; rewrite (HWA k Hk), (HWB k Hk); reflexivity).
  assert (Exu : x_uniq r u = x_uniq r w) by (unfold x_uniq; apply forall_nat_ext; intros i Hi; rewrite (HA i Hi), (HB i Hi); reflexivity).
  assert (Eyu : y_uniq q u = y_uniq q w) by (unfold y_uniq; apply forall_nat_ext; intros j Hj; rewrite (HY j Hj), (HYb j Hj); reflexivity).
  assert (EAB : all_X_true r u = all_X_true r w) by (unfold all_X_true; apply forall_nat_ext; intros i Hi; rewrite (HA i Hi), (HB i Hi); reflexivity).
  assert (EY : all_Y_true q u = all_Y_true q w) by (unfold all_Y_true; apply forall_nat_ext; intros j Hj; rewrite (HY j Hj), (HYb j Hj); reflexivity).
  assert (Edummy : is_dummy t r q u = is_dummy t r q w) by (unfold is_dummy; rewrite Hp, Ewok, EAB, EY; reflexivity).
  assert (Ephi : is_phi t r q u = is_phi t r q w) by (unfold is_phi; rewrite Ewu, Exu, Eyu; reflexivity).
  unfold C_p4. rewrite Hd, Hp, EY, Ewok, Exok, Ewu, EAB, HqB, Edummy, Ephi. reflexivity.
Qed.

Lemma agrees_on_same_inst : forall t r q s u w x S,
  same_inst_p4 t r q s u w -> (agrees_on t r q s u x S <-> agrees_on t r q s w x S).
Proof.
  intros t r q s u w x S [Hd [HqB [Hz0 [HWA [HWB [HA [HB [HY [HYb [HZ Hp]]]]]]]]]].
  unfold agrees_on. rewrite Hd, HqB, Hz0, Hp.
  split; intros [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 H11]]]]]]]]]]; repeat split; intros; auto.
  - rewrite <- (HWA k H); auto.
  - rewrite <- (HWB k H); auto.
  - rewrite <- (HA i H); auto.
  - rewrite <- (HB i H); auto.
  - rewrite <- (HY j H); auto.
  - rewrite <- (HYb j H); auto.
  - rewrite <- (HZ m H); auto.
  - rewrite (HWA k H); auto.
  - rewrite (HWB k H); auto.
  - rewrite (HA i H); auto.
  - rewrite (HB i H); auto.
  - rewrite (HY j H); auto.
  - rewrite (HYb j H); auto.
  - rewrite (HZ m H); auto.
Qed.

Definition agrees_bool (t r q s : nat) (w x : Inst) (S : Sub) : bool :=
  (negb (sd S) || Bool.eqb (fd w) (fd x)) &&
  (negb (sqB S) || Bool.eqb (fqB w) (fqB x)) &&
  (negb (sz0 S) || Bool.eqb (fz0 w) (fz0 x)) &&
  forall_nat t (fun k => negb (sWp S k) || Bool.eqb (fWp w k) (fWp x k)) &&
  forall_nat t (fun k => negb (sWm S k) || Bool.eqb (fWm w k) (fWm x k)) &&
  forall_nat r (fun i => negb (sXp S i) || Bool.eqb (fXp w i) (fXp x i)) &&
  forall_nat r (fun i => negb (sXm S i) || Bool.eqb (fXm w i) (fXm x i)) &&
  forall_nat q (fun j => negb (sYp S j) || Bool.eqb (fYp w j) (fYp x j)) &&
  forall_nat q (fun j => negb (sYm S j) || Bool.eqb (fYm w j) (fYm x j)) &&
  forall_nat s (fun m => negb (sZ S m) || Bool.eqb (fZ w m) (fZ x m)) &&
  (negb (sp S) || Bool.eqb (fp w) (fp x)).

Lemma bool_impl_eqb_iff : forall b1 b2 b3 : bool,
  (negb b1 || Bool.eqb b2 b3 = true) <-> (b1 = true -> b2 = b3).
Proof.
  intros b1 b2 b3. destruct b1; destruct b2; destruct b3; simpl; split; intro H;
    try reflexivity; try discriminate; try (intro; discriminate);
    try (pose proof (H eq_refl); discriminate); auto.
Qed.

Lemma nat_bool_impl_eqb_iff : forall n (sF wF xF : nat -> bool),
  (forall i, i < n -> negb (sF i) || Bool.eqb (wF i) (xF i) = true) <->
  (forall i, i < n -> sF i = true -> wF i = xF i).
Proof.
  intros n sF wF xF. split; intros H i Hi.
  - apply bool_impl_eqb_iff. exact (H i Hi).
  - apply bool_impl_eqb_iff. exact (H i Hi).
Qed.

Lemma agrees_bool_iff : forall t r q s w x S,
  agrees_bool t r q s w x S = true <-> agrees_on t r q s w x S.
Proof.
  intros t r q s w x S. unfold agrees_bool, agrees_on.
  repeat rewrite Bool.andb_true_iff.
  repeat rewrite forall_nat_iff.
  pose proof (bool_impl_eqb_iff (sd S) (fd w) (fd x)).
  pose proof (bool_impl_eqb_iff (sqB S) (fqB w) (fqB x)).
  pose proof (bool_impl_eqb_iff (sz0 S) (fz0 w) (fz0 x)).
  pose proof (nat_bool_impl_eqb_iff t (sWp S) (fWp w) (fWp x)).
  pose proof (nat_bool_impl_eqb_iff t (sWm S) (fWm w) (fWm x)).
  pose proof (nat_bool_impl_eqb_iff r (sXp S) (fXp w) (fXp x)).
  pose proof (nat_bool_impl_eqb_iff r (sXm S) (fXm w) (fXm x)).
  pose proof (nat_bool_impl_eqb_iff q (sYp S) (fYp w) (fYp x)).
  pose proof (nat_bool_impl_eqb_iff q (sYm S) (fYm w) (fYm x)).
  pose proof (nat_bool_impl_eqb_iff s (sZ S) (fZ w) (fZ x)).
  pose proof (bool_impl_eqb_iff (sp S) (fp w) (fp x)).
  tauto.
Qed.

Lemma filter_le : forall {A : Type} (L : list A) (p1 p2 : A -> bool),
  (forall a, In a L -> p1 a = true -> p2 a = true) ->
  length (filter p1 L) <= length (filter p2 L).
Proof.
  induction L as [|a rest IH]; intros p1 p2 H; simpl; [lia|].
  assert (Hr : length (filter p1 rest) <= length (filter p2 rest))
    by (apply IH; intros x Hx; apply H; right; exact Hx).
  destruct (p1 a) eqn:E1; destruct (p2 a) eqn:E2; simpl; try lia.
  pose proof (H a (or_introl eq_refl) E1) as Hbad. rewrite E2 in Hbad. discriminate.
Qed.

Lemma filter_strict_lt : forall {A : Type} (L : list A) (p1 p2 : A -> bool),
  (forall a, In a L -> p1 a = true -> p2 a = true) ->
  (exists v, In v L /\ p2 v = true /\ p1 v = false) ->
  length (filter p1 L) < length (filter p2 L).
Proof.
  induction L as [|a rest IH]; intros p1 p2 Hle [v [Hv1 [Hv2 Hv3]]]; simpl in *; [contradiction|].
  destruct Hv1 as [Heq | Hrest].
  - subst v. rewrite Hv2, Hv3. simpl.
    assert (Hr : length (filter p1 rest) <= length (filter p2 rest))
      by (apply filter_le; intros x Hx; apply Hle; right; exact Hx).
    lia.
  - assert (Hsub : length (filter p1 rest) < length (filter p2 rest)).
    { apply IH; [intros x Hx; apply Hle; right; exact Hx | exists v; auto]. }
    destruct (p1 a) eqn:E1; destruct (p2 a) eqn:E2; simpl; try lia.
    pose proof (Hle a (or_introl eq_refl) E1) as Hbad. rewrite E2 in Hbad. discriminate.
Qed.

Lemma filter_length_le : forall {A : Type} (L : list A) (p : A -> bool),
  length (filter p L) <= length L.
Proof.
  induction L as [|a rest IH]; intro p; simpl; [lia|].
  destruct (p a); simpl; pose proof (IH p); lia.
Qed.

Definition cov_count_p4 (t r q s : nat) (x : Inst) (S : Sub) : nat :=
  length (filter (fun u => C_p4 t r q u && agrees_bool t r q s u x S) (all_insts_p4 t r q s)).

Lemma strictly_subsumes_cov_lt : forall t r q s x S1 S2,
  strictly_subsumes t r q s x S2 S1 ->
  cov_count_p4 t r q s x S1 < cov_count_p4 t r q s x S2.
Proof.
  intros t r q s x S1 S2 [Hsub [v [HvC [Hv2 Hv1]]]].
  unfold cov_count_p4. apply filter_strict_lt.
  - intros a _ Ha. apply Bool.andb_true_iff in Ha. destruct Ha as [HaC Ha1].
    apply Bool.andb_true_iff. split; [exact HaC|].
    apply agrees_bool_iff. apply Hsub; [exact HaC | apply agrees_bool_iff; exact Ha1].
  - destruct (all_insts_p4_complete t r q s v) as [v0 [Hv0In Hsame]].
    exists v0. split; [exact Hv0In|]. split.
    + apply Bool.andb_true_iff. split.
      * rewrite (C_p4_same_inst t r q s v0 v Hsame). exact HvC.
      * apply agrees_bool_iff. apply (proj2 (agrees_on_same_inst t r q s v0 v x S2 Hsame)). exact Hv2.
    + destruct (agrees_bool t r q s v0 x S1) eqn:E1; [|rewrite Bool.andb_false_r; reflexivity].
      exfalso. apply Hv1. apply (proj1 (agrees_on_same_inst t r q s v0 v x S1 Hsame)).
      apply agrees_bool_iff. exact E1.
Qed.

Lemma strictly_subsumes_trans : forall t r q s x S3 S2 S1,
  strictly_subsumes t r q s x S3 S2 ->
  strictly_subsumes t r q s x S2 S1 ->
  strictly_subsumes t r q s x S3 S1.
Proof.
  intros t r q s x S3 S2 S1 [H32 _] [H21 [v [HvC [Hv2 Hv1]]]].
  split.
  - intros u HuC Hu1. apply H32; [exact HuC | apply H21; assumption].
  - exists v. split; [exact HvC | split; [apply H32; assumption | exact Hv1]].
Qed.

Lemma dec_exist_fair_at_to_pi : forall t r q s phi x,
  dec_exist_fair_at t r q s phi x ->
  exists S : Sub, is_fair_P4 S /\ is_pi t r q s phi x S.
Proof.
  intros t r q s phi x [S0 [HS0f [HS0w HS0no]]].
  assert (Hfind : forall S,
    is_fair_P4 S ->
    weak_axp t r q s phi x S ->
    (forall T, is_unfair_P4 T -> weak_axp t r q s phi x T -> ~ strictly_subsumes t r q s x T S) ->
    exists S_max,
      is_fair_P4 S_max /\
      weak_axp t r q s phi x S_max /\
      (forall T, weak_axp t r q s phi x T -> ~ strictly_subsumes t r q s x T S_max)).
  { intros S HSf HSw HSno.
    remember (length (all_insts_p4 t r q s) - cov_count_p4 t r q s x S) as m eqn:Hm.
    revert S Hm HSf HSw HSno.
    induction m as [m IH] using lt_wf_ind.
    intros S Hm HSf HSw HSno.
    destruct (classic (exists S1, is_fair_P4 S1 /\ weak_axp t r q s phi x S1 /\ strictly_subsumes t r q s x S1 S))
      as [[S1 [HS1f [HS1w HS1sub]]] | Hno_fair].
    - assert (Hcnt : cov_count_p4 t r q s x S < cov_count_p4 t r q s x S1) by (apply strictly_subsumes_cov_lt; exact HS1sub).
      assert (Hbd1 : cov_count_p4 t r q s x S1 <= length (all_insts_p4 t r q s)) by (unfold cov_count_p4; apply filter_length_le).
      assert (Hm1 : length (all_insts_p4 t r q s) - cov_count_p4 t r q s x S1 < m) by lia.
      apply (IH _ Hm1 S1 eq_refl HS1f HS1w).
      intros T HTu HTw Hsub1. apply (HSno T HTu HTw).
      exact (strictly_subsumes_trans t r q s x T S1 S Hsub1 HS1sub).
    - exists S. split; [exact HSf | split; [exact HSw |]].
      intros T HTw HsubT.
      destruct (sp T) eqn:Ep.
      + exact (HSno T Ep HTw HsubT).
      + apply Hno_fair. exists T. split; [exact Ep | split; assumption]. }
  destruct (Hfind S0 HS0f HS0w HS0no) as [Smax [HSmaxf [HSmaxw HSmaxno]]].
  destruct (weak_axp_has_axp t r q s phi x Smax HSmaxw) as [Saxp [Hle Haxp]].
  exists Saxp. split.
  - destruct (sp Saxp) eqn:Ep; [|exact Ep].
    destruct Hle as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ L11]]]]]]]]]].
    pose proof (L11 Ep) as Htmp. congruence.
  - split; [exact Haxp|].
    intros T [HTw _] [HcovT [v [HvC [HvT HvnS]]]].
    apply (HSmaxno T HTw). split.
    + intros u HuC HuMax. apply HcovT; [exact HuC | exact (agrees_sub_le t r q s u x Saxp Smax Hle HuMax)].
    + exists v. split; [exact HvC | split; [exact HvT |]].
      intro HvMax. apply HvnS. exact (agrees_sub_le t r q s v x Saxp Smax Hle HvMax).
Qed.

Lemma dec_exist_fair_at_from_pi : forall t r q s phi x,
  (exists S : Sub, is_fair_P4 S /\ is_pi t r q s phi x S) ->
  dec_exist_fair_at t r q s phi x.
Proof.
  intros t r q s phi x [S [HSf [[HSw _] HnoSub]]].
  exists S. split; [exact HSf | split; [exact HSw |]].
  intros T _ HTw [HcovT [v [HvC [HvT HvnS]]]].
  destruct (weak_axp_has_axp t r q s phi x T HTw) as [T' [HTle HTaxp]].
  apply (HnoSub T' HTaxp). split.
  - intros u HuC HuS. exact (agrees_sub_le t r q s u x T' T HTle (HcovT u HuC HuS)).
  - exists v. split; [exact HvC | split; [exact (agrees_sub_le t r q s v x T' T HTle HvT) | exact HvnS]].
Qed.

(* ========================================================================= *)
(* Main Equivalence Theorems: P4 is Pi_4^P-complete (Literal Def 3, 4, 15)   *)
(* ========================================================================= *)

Theorem p4_pi4p_equiv : forall t r q s phi,
  1 <= t -> 1 <= r ->
  cnf_bounded (t + r + q + s) phi ->
  (cls_exist_fair t r q s phi <-> four_qbf t r q phi).
Proof.
  intros t r q s phi Ht Hr Hbnd. split.
  - exact (cls_exist_fair_implies_four_qbf t r q s phi Hr Hbnd).
  - exact (four_qbf_implies_cls_exist_fair t r q s phi Ht Hr Hbnd).
Qed.

Theorem p4_pi4p_equiv_literal : forall t r q s phi,
  1 <= t -> 1 <= r ->
  cnf_bounded (t + r + q + s) phi ->
  (cls_exist_fair_pi t r q s phi <-> four_qbf t r q phi).
Proof.
  intros t r q s phi Ht Hr Hbnd.
  rewrite <- (p4_pi4p_equiv t r q s phi Ht Hr Hbnd). split.
  - intros Hpi x HxC. apply dec_exist_fair_at_from_pi. exact (Hpi x HxC).
  - intros Hwk x HxC. apply dec_exist_fair_at_to_pi. exact (Hwk x HxC).
Qed.

Print Assumptions p4_constrained_ftu.
Print Assumptions p4_pi4p_equiv_literal.
Print Assumptions p4_pi4p_equiv.
