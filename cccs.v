
Variable A : Type.

Inductive Obj : Type :=
| base : A -> Obj
| terminal : Obj
| prod : Obj -> Obj -> Obj
| exp  : Obj -> Obj -> Obj
.

Coercion base : A >-> Obj.

Notation "a 'x' b" := (prod a b) (at level 32).

(* Variables a b : A. *)

(* Check (a x b). *)

Notation "a ==> b" := (exp a b)(at level 33, right associativity).

Notation "1" := terminal.

(* Check (a ==> b x 1). *)

(* This is the "type theoretic" version, which
   implicitely uses Yoneda everywhere... *)
Inductive Mor : Obj -> Obj -> Type :=
| ident : forall {a}, Mor a a
| comp  : forall {a b c}, Mor a b -> Mor b c -> Mor a c
| final : forall a, Mor a 1
| pair  : forall {g a b}, Mor g a -> Mor g b -> Mor g (a x b)
| pi_1  : forall {g a b}, Mor g (a x b) -> Mor g a
| pi_2  : forall {g a b}, Mor g (a x b) -> Mor g b
| lam   : forall {g a b}, Mor (g x a) b -> Mor g (a ==> b)
| app   : forall {g a b}, Mor g (a ==> b) -> Mor g a -> Mor g b
.

(* No notion of opp! Or indeed, Mor actions *)
Definition Psh := Obj -> Type.

(* But we can define what it means to have one! *)
Definition map_F (F : Psh) := forall a b (f : Mor a b), F b -> F a.

Definition Yoneda : Obj -> Psh :=
  fun a => (fun b => Mor b a).

Definition transport_y : forall a b (f : Mor a b),
    forall c, Yoneda a c -> Yoneda b c.
Proof.
  unfold Yoneda; intros.
  eapply comp; eauto.
Defined.

Print transport_y.


Definition map_y : forall a, map_F (Yoneda a).
Proof.
  intros.
  unfold map_F.
  unfold Yoneda.
  intros.
  exact (comp f X).
Defined.

Print map_y.

Open Scope type_scope.

Definition Nat (F G : Psh) : Type := forall a, F a -> G a.

Definition Exp : Psh -> Psh -> Psh :=
  fun F G a =>
    forall b, (Yoneda a b * F b -> G b).

Definition map_exp : forall F G, map_F F -> map_F G -> map_F (Exp F G).
Proof.
  unfold map_F.
  intros F G map_f map_g c1 c2 f.
  unfold Exp.
  intros alpha d.
  generalize (transport_y _ _ f d).
  intros y_f [g m].
  pose (h := (y_f g)).
  apply alpha; auto.
Defined.


Fixpoint obj_interp (a : Obj) : Psh :=
  match a with
  | base a => Yoneda a
  | 1 => (fun o => unit)
  | a x b => fun o => (obj_interp a o) * (obj_interp b o)
  | a ==> b => Exp (obj_interp a) (obj_interp b)
  end.

Definition map_obj_interp : forall a, map_F (obj_interp a).
Proof.
  induction a; generalize map_y; unfold map_F; simpl.
  - intros.
    eapply X; [exact f| exact X0].
  - intros.
    exact H.
  - unfold map_F in *.
    intros.
    destruct X0.
    split; [eapply IHa1; [exact f| exact o] | eapply IHa2; [exact f| exact o0]].
  - intros.
    generalize (map_exp (obj_interp a1) (obj_interp a2)).
    unfold map_F in *.
    intros.
    eapply X1; intros; eauto.
Defined.

Print map_obj_interp.

Notation "〚 a 〛" := (obj_interp a).

Definition reify_y : forall {a b}, Nat (Yoneda a) (Yoneda b) -> Mor a b.
Proof.
  intros a b; unfold Nat.
  intros transp; apply (transp _ ident).
Defined.

Definition mor_interp {a b} (f: Mor a b) : Nat 〚 a 〛 〚 b 〛.
Proof.
  induction f; unfold Nat; simpl.
  - intros a0 m; exact m.
  - intros g m.
    unfold Nat in *.
    apply IHf2.
    apply IHf1.
    exact m.
  - intros.
    exact tt.
  - intros.
    split.
    + apply IHf1.
      exact X.
    + apply IHf2; exact X.
  - unfold Nat in *; simpl in *.
    apply IHf.
  - unfold Nat in *; simpl in *.
    apply IHf.
  - unfold Exp.
    unfold Nat in *.
    simpl in *.
    intros.
    apply IHf; auto.
    destruct X0 as (m, n); split; [|exact n].
    eapply map_obj_interp; [exact m| exact X].
  - unfold Nat in *; simpl in *; unfold Exp in *.
    intros.
    eapply IHf1; [exact X|].
    split; [exact ident| apply IHf2; exact X].
Defined.

Print mor_interp.

Notation "(| f |)" := (mor_interp f).

Definition id_Nat : forall F, Nat F F.
Proof.
  unfold Nat; intros; firstorder.
Defined.

Hint Resolve id_Nat.

Definition comp_Nat : forall {F G H}, Nat F G -> Nat G H -> Nat F H.
Proof.
  unfold Nat; intros; auto.
Defined.

Print comp_Nat.

(* This should exist by fiat? *)
Definition q_q_inv {a} : Nat 〚 a 〛 (Yoneda a)
                         *
                         Nat (Yoneda a) 〚 a 〛.
Proof.
  induction a; split; simpl; unfold Nat; unfold Yoneda.
  - intros b f; exact f.
  - intros b f; exact f.
  - intros.
    apply final.
  - intros; exact tt.
  - intros a [f g]; apply pair.
    + apply IHa1; auto.
    + apply IHa2; auto.
  - intros.
    split.
    + apply IHa1.
      eapply pi_1; eauto.
    + apply IHa2; eapply pi_2; eauto.
  - intros; apply lam.
    apply IHa2.
    apply X.
    split.
    + eapply pi_1; exact ident.
    + apply IHa1.
      eapply pi_2; exact ident.
  - intros.
    unfold Exp.
    intros b [f m]; apply IHa2.
    eapply app.
    + eapply transport_y.
      -- exact X.
      -- exact f.
    + apply IHa1.
      exact m.
Defined.

Notation "'q'" := (fst q_q_inv).

Notation "'q⁻'" := (snd q_q_inv).

Check q⁻.
Check q.

Check comp_Nat.

Check reify_y.

Print reify_y.

Check comp_Nat.

Notation "m ∘ n" := (comp_Nat n m)(at level 50).

Check q⁻.


Definition nf {a b : Obj} (f : Mor a b) :=
  let up_down := q ∘ (| f |) ∘ q⁻
  in
  reify_y up_down
.

  (* q _ ( (| f |) _ (q⁻ _ ident)). *)

Check nf.

Variable a b : A.


Definition test : Mor 1 (a ==> a).
Proof.
  apply lam.
  eapply comp.
  eapply pi_2.
  exact ident.
  apply ident.
Defined.

Definition test' : Mor 1 (a ==> a).
Proof.
  apply lam.
  eapply pi_2; apply ident.
Defined.

Goal (nf test = nf test').
Proof.
  vm_compute.
  reflexivity.
Qed.

Definition test'' : Mor 1 (a ==> b ==> b x a).
Proof.
  apply lam.
  apply lam.
  eapply pair.
  - eapply pi_2.
    exact ident.
  - eapply pi_2.
    eapply pi_1.
    exact ident.
Defined.

Definition test''' : Mor (a ==> b ==> b x a) (a ==> b ==> a).
Proof.
  apply lam.
  apply lam.
  eapply pi_2.
  eapply app.
  eapply app.
  eapply pi_1.
  eapply pi_1.
  exact ident.
  eapply pi_2.
  eapply pi_1.
  exact ident.

  eapply pi_2.
  exact ident.
Defined.

Print test'.

Definition test'''' : Mor 1 (a ==> b ==> a).
Proof.
  apply lam.
  apply lam.
  eapply pi_2.
  eapply pi_1.
  exact ident.
Defined.

Check test''.

Definition foo := comp test'' test'''.

Check (q⁻ _ ident).

Check ((| foo |) _ (q⁻ _ ident)).

Eval compute in ( q _ ((| foo |) _ (q⁻ _ ident))).

Eval compute in nf (nf foo).

Eval vm_compute in comp test'' test'''.
(* Set Printing Implicit. *)
Eval vm_compute in (nf (comp test'' test''')).
Eval vm_compute in (nf (nf (comp test'' test'''))).
Eval vm_compute in (nf test'''').

Goal (nf (comp test'' test''') = nf test'''').
  vm_compute.
  (* Uh oh *)
  Fail reflexivity.
Abort.

Definition blah : Mor a a.
  eapply pi_1.
  eapply pi_1.
  eapply comp.
  eapply pair.
  eapply pair.
  exact ident.
  exact ident.
  exact ident.
  exact ident.
Defined.

Print blah.

Eval compute in (nf blah).