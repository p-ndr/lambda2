(* Midterm Project for Logic Programming, Parnian Naderi, 610301075 *)

Import Nat.

Require Import List.
Import List.ListNotations.

Definition termorder := nat.
Definition typeorder := nat.


Inductive T2 : Type :=
| var: typeorder -> T2
| arrow: T2 -> T2 -> T2
| abst: typeorder -> T2 -> T2
.

Inductive term: Type :=
| tvar: termorder -> term
| tapp: term -> term -> term 
| tyapp: term -> T2 -> term 
| tabst: termorder -> term -> term
| tyabst: typeorder -> term -> term.

Inductive statement : Type :=
| term_type : term -> T2 -> statement
| type_type : T2 -> statement.

Inductive declaration : Type := 
| dectm : termorder -> T2 -> declaration
| decty : typeorder -> declaration.

Definition context : Type := list declaration.

Fixpoint freevarlist (r:T2) : list typeorder :=
    match r with
    | var ty => [ty]
    | arrow t1 t2 => (freevarlist t1) ++ (freevarlist t2)
    | abst v t1 => remove PeanoNat.Nat.eq_dec v (freevarlist t1)
    end.

Fixpoint type_eq (ty1 ty2: T2) : bool :=
    match ty1, ty2 with
    | var a, var b => eqb a b
    | arrow a b, arrow a' b' => (type_eq a a') && (type_eq b b')
    | abst a b, abst a' b' => (eqb a a') && (type_eq b b')
    | _, _ => false 
    end.

Fixpoint term_eq (t1 t2: term) : bool :=
    match t1, t2 with
    | tvar a, tvar b => eqb a b 
    | tapp a b, tapp a' b' => (term_eq a a') && (term_eq b b')
    | tyapp a b, tyapp a' b' => (term_eq a a') && (type_eq b b')
    | tabst a b, tabst a' b' => (eqb a a') && (term_eq b b')
    | tyabst a b, tyabst a' b' => (eqb a a') && (term_eq b b')
    | _, _ => false 
    end.

Fixpoint check_term (v : term) (con : context) : bool := 
    match con with
    | nil => false
    | x :: l => match x with  
                | dectm a b => (term_eq v (tvar a)) || (check_term v l)
                | decty a => check_term v l
    end
    end.

Fixpoint check_type (to : typeorder) (con : context) : bool :=
    match con with
    | nil => false
    | x :: l => match x with
                | dectm a b => check_type to l
                | decty a => (eqb a to) || (check_type to l)
    end
    end.

Fixpoint foreach {X : Type} (l : list X) (p : X -> bool) : bool :=
    match l with
    | nil => false
    | a :: l' => (p a) && (foreach l' p)
    end.

Inductive validl2context : context -> Prop := 
| empty : validl2context []
| add_type : forall (to : typeorder) (gamma : context), validl2context gamma -> (check_type to gamma = false)
                                                        -> validl2context (decty to :: gamma)
| add_var : forall (tmo : termorder) (gamma : context) (rho : T2), validl2context gamma -> (check_term (tvar tmo) gamma = false)
                                                                    -> (foreach (freevarlist rho) (fun x : typeorder => check_type x gamma)) = true
                                                                    -> validl2context (dectm tmo rho :: gamma)
.

Fixpoint typereplacement (A : T2) (B : T2) (alpha : typeorder) : T2 :=
    match A with
    | var x => if eqb x alpha then B else A
    | arrow x y => arrow (typereplacement x B alpha) (typereplacement y B alpha)
    | abst x t => if eqb x alpha then A else abst x (typereplacement t B alpha)
    end.

Inductive inferencerule : context -> statement -> Prop :=
| ivar : forall (gamma : context) (sigma : T2) (x : termorder), (validl2context gamma) -> (In (dectm x sigma) gamma)
                                                                                       -> inferencerule gamma (term_type (tvar x) sigma)
| iappl : forall (gamma : context) (sigma tau : T2) (M N: term), (inferencerule gamma (term_type M (arrow sigma tau)))
                                                                -> (inferencerule gamma (term_type N sigma))
                                                                -> (inferencerule gamma (term_type (tapp M N) tau))
| iabst : forall (gamma : context) (sigma tau : T2) (x : termorder) (M : term), (inferencerule ((dectm x sigma) :: gamma) (term_type M tau))
                                    -> (inferencerule gamma (term_type (tabst x M) (arrow sigma tau)))
| iform : forall (gamma : context) (B : T2), (validl2context gamma) -> (foreach (freevarlist B) (fun x : typeorder => check_type x gamma)) = true
                                                                    -> inferencerule gamma (type_type B)
| iappl2 : forall (gamma : context) (M : term) (A B: T2) (alpha : typeorder), (inferencerule gamma (term_type M (abst alpha A)))
                                                    -> (inferencerule gamma (type_type B))
                                                    -> (inferencerule gamma (term_type (tyapp M B) (typereplacement A B alpha)))
| iabst2 : forall (gamma : context) (A : T2) (alpha : typeorder) (M : term),
            (inferencerule ((decty alpha ) :: gamma) (term_type M A))
            -> (inferencerule gamma (term_type (tyabst alpha M) (abst alpha A))).

Lemma context_term : forall (gamma : context) (x : termorder) (sigma : T2),
    validl2context ((dectm x sigma) :: gamma) -> validl2context gamma.
 Proof.
    intros gamma x sigma H. inversion H. apply H3. Qed.

Lemma context_type : forall (gamma : context) (x : typeorder),
validl2context ((decty x) :: gamma) -> validl2context gamma.
Proof.
    intros gamma x H. inversion H. apply H2. Qed.

Theorem exercise19: forall (gamma : context) (L : term) (sigma : T2),
    (inferencerule gamma (term_type L sigma)) -> (validl2context gamma).
Proof.
    intros gamma L sigma H. 
    induction H.
    - apply H.
    - apply IHinferencerule1.
    - apply (context_term gamma x sigma0). apply IHinferencerule.
    - apply H.
    - apply IHinferencerule1.
    - apply (context_type gamma alpha). apply IHinferencerule. Qed.
