(** V tej lekciji bomo spoznali induktivne tipe.

    Najbolj znan primer induktivnega tipa so naravna števila.
    Drugi znani primeri so seznami in drevesa.

    Induktivni tip [T] definiran tako, da podamo nekaj
    _konstruktorjev_ (ki nimajo zveze s konstruktorji
    v objektnem programiranju)

      c_1 : ... -> T
      c_2 : ... -> T
      ...
      c_n : ... -> T

    Vsak od konstruktorjev sprejme še nič ali več argumentov
    različnih tipov (zgoraj označeno z ...). Nekateri argumenti
    so lahko spet tipa [T] (ali celo bolj splošni, v kar se tu ne
    bomo spuščali), zato so induktivni tipi _rekurzivni_.

    Elementi tipa [T] so vsi tisti izrazi oblike [c_i e_1 .. e_k]
    za katere so [e_1, ..., e_k] ustrezni argumenti in je [c_i]
    eden od konstruktorjev. Drugač povedano, elemente [T] gradimo
    _indkutivno_, začenši s konstruktorji brez argumentov.

    Na primer, naravna števila lahko definiramo takole.
*)

Inductive N :=
  | o : N
  | s : N -> N.

(** Imamo dva konstruktorja. Konstruktor [o] ne sprejme nobenega
    parametra, torej je to _konstanta_ tipa [nat]. Konstruktor [s]
    sprejme kot argument naravno število. Katere elemente lahko
    zgradimo s pomočjo teh dveh konstruktorjev? *)

Check o.
Check s o.
Check s (s o).
Check s (s (s o)).
Check s (s (s (s o))).

(** Res dobivamo naravna števila. Ker je tip _indkutiven_
    "neskončni" izraz [s (s (s (s ...)))], v katerem se [s]
    v nedogled ponavlja, _ni_ veljaven. Coq pozna tudi _koinduktivne_
    tipe, ki vsebujejo tudi neskončne izraze.
*)

(** Tudi seznami so induktivni tip. Takole definiramo sezname,
    ki imajo elemente tipa [A]:  *)

Inductive seznam (A : Type) :=
  | prazen : seznam A
  | sestavi : A -> seznam A -> seznam A.

(** To definicijo preberemo takole: definirali smo
    induktivni tip [seznam], ki je parameteriziran s
    tipom [A]. To pomeni, da za vsak tip [A] dobimo
    tip [seznam A]. Elementi tipa [seznam A] so:

    - [prazen A] je element tipa [seznam A],
    - [sestavi A x l] je element tipa [seznam A], pri predpostavki
      da je [x : A] in [l : seznam A].

    Tu je nekaj seznamov tipa [seznam bool]. *)

Check prazen bool. (* prazen seznam *)
Check sestavi bool false (sestavi bool true (prazen bool)). (* seznam [false, true] *)

(* Kot vidimo, je treba vedno povedati tip [A], kar je precej
   nepraktično. Coq-u lahko razložimo, da naj bo [A] impicitni argument
   pri konstruktorjih [prazen] in [sestavi].
   Tako ga bo Coq sam izračunal iz ostalih podatkov (ali se pritožil,
   če ne bo znal. *)

Arguments prazen {A}.
Arguments sestavi {A} _ _.

(** Sedaj lahko pišemo krajše: *)

Check @prazen bool. (* prazen seznam elementov tipa [bool]. *)
Check sestavi false (sestavi true prazen). (* seznam [false, true] *)

(** Pri praznem seznamu smo morali še vedno pisati [bool], saj sicer
    Coq ne more uganiti, da gre za prazen seznam elementov tipa [bool]. *)

(** Coq pravzaprav že ima definirana naravna števila in sezname. *)
Print nat.
Print list.

(** Za naravna števila ima Coq običajno notacijo. *)
Check 42.

(** Za sezname uporablja enako notacijo kot OCaml. *)
Check @nil bool.
Check cons false (cons true nil). (* seznam [false, true] *)

(** Namesto [cons x xs] lahko pišemo [x :: xs], če aktiviramo
    notacijo iz [list_scope]. *)
Check (false :: true :: nil)%list.
Local Open Scope list_scope.
Check false :: true :: nil.

(** Od sedaj naprej bomo uporabljali Coq-ova tipa [nat] in [list]. *)

Require Import Arith. (* Knjižnica izrekov o [nat]. *)
Require Import List.  (* Knjižnica izrekov o [list]. *)

(** Funkcije na induktivnih tipih definiramo rekurzivno.
    Rekurzivne funkcije definiramo s [Fixpoint] ali [fix].
*)

Fixpoint dolzina {A : Type} (lst : list A) : nat :=
  match lst with
    | nil => 0
    | _ :: lst' => S (dolzina lst')
  end.

(** Ekvivalentna defincija s [fix]. Ta je podoben kot
    [fun], saj definira anonimno funkcijo. V spodnji
    definiciji je [f] vezana spremenljivka. 
*)
Definition dolzina' {A: Type} :=
   fix f (lst : list A) : nat :=
     match lst with
       | nil => 0
       | _ :: lst' => S (f lst')
     end.

(** Primer računanja s funkcijo [dolzina]. *)
Eval compute in dolzina (2 :: 4 :: 3 :: nil).

(** V standardni knjižnici je funkcija za dolžino seznama že definirana. *)
Print length.

Eval compute in length (2 :: 4 :: 3 :: nil).

(** Sestavi funkcijo [range n], ki vrne seznam naravnih števil
    [(n-1) :: (n-2) :: ... 1 :: 0 :: nil]. 

    [Definition] spremeni v [Fixpoint] ali pa uporabo [fix].
*)
Definition range : nat -> list nat.
Admitted.

(*
  Fixpoint range (n : nat) :=
    ???
*)

(** Naslednji izračun mora vrniti
    9 :: 8 :: 7 :: 6 :: 5 :: 4 :: 3 :: 2 :: 1 :: 0 :: nil *)
Eval compute in range 10.

(** Definirajmo še funkcijo za stikanje dveh seznamov. *)
Fixpoint stakni {A : Type} (lst1 : list A) (lst2 : list A) : list A :=
  match lst1 with
    | nil => lst2
    | x :: lst1' => x :: (stakni lst1' lst2)
  end.

Eval compute in stakni (range 5) (range 7).

(* Coq ne dovoli definirati rekurzivne funkcije, ki ni povsod definirana.
   Zato moramo vedno zagotoviti, da se rekurzivni klici izvajajo na manjših
   argumentih. Coq sam ugotovi, kateri argument se zmanjšuje. Če tega ne
   zna sam, mu lahko to povemo z določilom [{struct ..}]. Recimo:
*)

Fixpoint stakni' {A : Type} (lst1 : list A) (lst2 : list A) {struct lst1}: list A :=
  match lst1 with
    | nil => lst2
    | x :: lst1' => x :: (stakni' lst1' lst2)
  end.

(** V standardni knjižnici že imamo funkcijo [app], ki stika sezname.
    Namesto [app x lst] lahko pišemo [x ++ lst]. *)
Print app.

Eval compute in range 5 ++ range 7.

(** Naloga: definiraj funkcijo, ki obrne seznam.
    Koda naj ustreza naslednji definiciji:
 
    - obrnjeni prazen seznam je spet prazen seznam
    - seznam x :: l' obrnemo tako, da obrnemo l' in ga staknemo
      s seznamom, ki vsebuje samo x.

    Nato v standardni knjižnici poišči funkcijo, ki obrača sezname.
    Primerjaj definicijo. *)
Definition obrni {A : Type} (lst : list A) : list A.
Admitted.

(* 
  Fixpoint obrni {A : Type} (lst : list A) :=
  ???
*)


(** Tole mora izračunati 5 :: 4 :: 3 :: 2 :: 1 :: nil *)
Eval compute in obrni (1 :: 2 :: 3 :: 4 :: 5 :: nil).

(** V standradni knjižnici poišči funkcijo za obračanje seznamov. *)

(** Izreke o induktivnih tipih dokazujemo z indukcijo.
    Vsak induktivni tip ima namreč pripadajoči princip indukcije.
    Indukcija na naravnih številih je le poseben primer splošne indukcije.

    Ko definiramo induktivni tip, Coq sam generira nekaj variant ustreznih
    principov indukcije. S taktiko [induction] lahko uporabimo tako generirani
    princip.
*)

(** Z indukcijo dokažimo, da je stik seznama [lst] in praznega seznama spet [lst]. *)
Lemma app_nil (A : Type) (lst : list A) : lst = lst ++ nil.
Proof.
  (* Indukcija na lst. *)
  induction lst.
  - (* osnovni primer: prazen seznam *)
    reflexivity.
  - (* indukcijski korak: seznam oblike [a :: lst] *)
    simpl.
    rewrite <- IHlst.
    reflexivity.
Qed.

(** Z indukcijo pokažimo, da velja [rev (lst1 ++ lst2) = (rev lst2) ++ (rev lst1)]. *)
Lemma rev_app (A : Type) (lst1 lst2 : list A) : rev (lst1 ++ lst2) = rev lst2 ++ rev lst1.
Proof.
  induction lst1.
  - apply app_nil.
  - simpl.
    (* Menda obstaja lema, da je [app] asociativen. *)
    SearchAbout (?x ++ ?y ++ ?z).
    rewrite app_assoc.
    rewrite <- IHlst1.
    reflexivity.
Qed.

(** Z indukcijo dokaži, da je dvakrat obrnjeni seznam enak prvotnemu. *)
Lemma rev_rev (A : Type) (lst : list A) : lst = rev (rev lst).
Proof.
  admit.
Qed.

(** Obravnavajmo še dvojiška drevesa. *)
Inductive tree :=
  | empty : tree
  | node : tree -> tree -> tree.

(** Število elementov v drevesu. *)
Fixpoint size (t : tree) :=
  match t with
    | empty => 0
    | node l r => S (size l + size r)
  end.

(** Globina drevesa. *)
Fixpoint depth (t : tree) :=
  match t with
    | empty => 0
    | node l r => S (max (depth l) (depth r))
  end.

(** Polno drevo globine n. *)
Fixpoint complete (n : nat) : tree :=
  match n with
    | 0 => empty
    | S n' => node (complete n') (complete n')
  end.

Eval compute in complete 3.
Eval compute in depth (complete 5).
Eval compute in size (complete 5).

(** Dokažimo, da ima [complete n] res globino [n] in da ima
     velikost [2^n - 1]. Potenciranje se skriva v knjižnici [NPeano]. *)

Require Import NPeano.

(** Vaja. *)
Lemma complete_depth (n : nat) : depth (complete n) = n.
Proof.
  admit.
Qed.

(** To naredimo skupaj na predavanjih. *)
Lemma complete_size (n : nat) : S (size (complete n)) = 2 ^ n.
Proof.
  induction n.
  - auto.
  - simpl.
    ring_simplify.
    SearchAbout (?x * ?y + ?x).
    rewrite <- mult_succ_r.
    congruence.
Qed.

(** Funkcija, ki zamenja levo in desno podrevo, in naredi
    isto še v obeh podrevesih. *)    
Fixpoint flip (t : tree) :=
  match t with
    | empty => empty
    | node l r => node (flip r) (flip l)
  end.

(** Če obrnemo dvakrat, dobimo isto drevo. *)
Lemma flip_idem (t : tree) : flip (flip t) = t.
Proof.
  admit.
Qed.

(** Obračanje ne spremeni velikosti. *)
Lemma flip_size (t : tree) : size t = size (flip t).
Proof.
  admit.
Qed.

(** Obrnjeno polno drevo je spet polno drevo. *)
Lemma flip_complete (n : nat) : complete n = flip (complete n).
Proof.
  admit.
Qed.

(** Pri naslednji nalogah ne potrebuješ indukcije, ker so
    indukcijske hipoteze neuporabne. Namesto [induction t]
    raje poskusi [destruc t] ali [destruct t as [|u1 u2]]. *)

(** Edino drevo globine 0 je prazno drevo. *)
Lemma globina_0 (t : tree) : depth t = 0 -> t = empty.
Proof.
  admit.
Qed.

(** Edino drevo globine 1 je [node empty empty]. *)
Lemma globina_1 (t : tree) :
  depth t = 1 -> t = node empty empty.
Proof.
  admit.
Qed.

(** Obstajajo tri drevesa globine 2. *)
Lemma globina_2 (t : tree) :
  depth t = 2 ->
  t = node (node empty empty) empty \/
  t = node empty (node empty empty) \/
  t = node (node empty empty) (node empty empty).
Proof.
  intro H.
  destruct t as [|t1 t2] ; try discriminate || auto.
  admit.
Qed.
