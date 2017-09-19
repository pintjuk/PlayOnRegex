open HolKernel Parse boolLib bossLib
open pred_setSyntax pred_setLib listTheory rich_listTheory listTheory pred_setTheory arithmeticTheory
open EmitML basis_emitTheory

val _ = new_theory "regexp"

(* =========================== *)
(*    DEFINITION OF REGEX    *)
(* =========================== *)

val Regex = Datatype `Reg = Eps
                          | Sym 'a
                          | Alt Reg Reg
                          | Seq Reg Reg
                          | Rep Reg`;

(* =========================== *)
(*    REGEX Semantix         *)
(* =========================== *)

val LANGUAGE_OF_def = Define
  `(language_of Eps = {[]}) /\
   (language_of (Sym c) = {[c]}) /\
   (language_of (Alt a b) = (language_of a) UNION (language_of b) ) /\
   (language_of (Seq f s) =
     {fstPrt ++ sndPrt | (fstPrt IN language_of f) /\
                         (sndPrt IN language_of s) } ) /\
   (language_of (Rep r) =
     {x| ?words. (EVERY (\e. e IN language_of r) words) /\
                 ((FLAT words)=x)})`;

EVAL ``[1;3] IN (language_of (Seq (Alt (Sym 1) (Sym 2)) (Sym 3)))``;
EVAL ``language_of (Rep (Alt (Sym 1) (Sym 2)))``;


val SanityRep = prove(
  ``[1;2;1;1] IN language_of (Rep (Alt (Sym 1) (Sym 2)))``,
  Ho_Rewrite.REWRITE_TAC [LANGUAGE_OF_def,IN_GSPEC_IFF]>>
  Q.EXISTS_TAC `[[1];[2];[1];[1]]` >>
  SIMP_TAC list_ss []
);

val SanitySeq1 = prove(
  ``[1;2] IN language_of (Seq (Sym 1)(Sym 2))``,
  Ho_Rewrite.REWRITE_TAC [LANGUAGE_OF_def,IN_GSPEC_IFF]>>
  REWRITE_TAC [
    SET_SPEC_CONV
      ``[1; 2] IN {fstPrt ++ sndPrt | fstPrt IN {[1]} /\ sndPrt IN {[2]}}``
  ]>>
  SIMP_TAC list_ss []
);

val AND_FOLD_FALSE_thm = prove(
  ``!a. ~(FOLDL $/\ F a)``,
  Induct >> ASM_SIMP_TAC std_ss [FOLDL]
);

val SanityRepNullable = prove(
  ``([] IN language_of (Rep (Alt (Sym 1) (Sym 2))))``,
  Ho_Rewrite.REWRITE_TAC [LANGUAGE_OF_def,IN_GSPEC_IFF, NOT_EXISTS_THM]>>
  Q.EXISTS_TAC `[]`>>
  SIMP_TAC list_ss []
);

val SanityRepNullable = prove(
  ``!R. ([] IN language_of (Rep R))``,
  Induct>>
  Ho_Rewrite.REWRITE_TAC [LANGUAGE_OF_def,IN_GSPEC_IFF]>>
  TRY STRIP_TAC>>
  Q.EXISTS_TAC `[]`>>
  SIMP_TAC (list_ss) []
);

(* =========================== *)
(* Executable model of regex *)
(* =========================== *)

val SPLIT_def = Define
  `(split []    = [([],[])]) /\
   (split (c::cs) = ([],c::cs)::(MAP (\x. (c::(FST x), SND x)) (split cs)))`;

val MEM_SPLIT_APPEND_THM = store_thm(
  "SPLIT_APPEND_THM",
  ``!A B. MEM (A,B) (split (A++B))``,

Induct >| [
  Cases >> SIMP_TAC list_ss [SPLIT_def],
  ASM_SIMP_TAC (list_ss++QI_ss) [SPLIT_def, MEM_MAP]
]);



val SPLIT_APPEND_THM =  store_thm(
  "SPLIT_APPEND_THM",
  ``!l l1 l2. (MEM (l1, l2) (split l)) <=> (l1 ++ l2 = l)``,
  SIMP_TAC std_ss [boolTheory.EQ_IMP_THM, FORALL_AND_THM] >>
  (Tactical.REVERSE CONJ_TAC) >-(
    Induct >- (
      Cases >> SIMP_TAC list_ss [SPLIT_def]
    )>>
    ASM_SIMP_TAC (list_ss++QI_ss) [SPLIT_def, MEM_MAP]
  )>>
  Induct>-(
     ASM_SIMP_TAC (list_ss) [SPLIT_def]
  )>>

  ASM_SIMP_TAC (list_ss) [SPLIT_def, MEM_MAP]>>
  REPEAT STRIP_TAC>>
  FULL_SIMP_TAC list_ss []
);

EVAL ``split []``;
EVAL ``split [x]``;
EVAL ``split [x;y;z]``;


(* It was pritty hard to work with this definition,
   maybe i should redefine this  *)
val PARTS_def = Define
  `(parts []     = [[]]) /\
   (parts (c::cs) =
     if cs = []
     then [[[c]]]
     else FLAT (MAP (\x. [[c]::x; (c::(HD x))::(TL x)]) (parts cs)))
   `;

val PARTS_SPEC = store_thm ("PARTS_SPEC",
  ``!(l:'a list) ll. MEM ll (parts l) <=> (~(MEM [] ll) /\ (FLAT ll = l))``,
Induct >- (
  SIMP_TAC list_ss [PARTS_def, FLAT_EQ_NIL, EVERY_MEM] >>
  Cases_on `ll` >| [
    SIMP_TAC list_ss [],

    SIMP_TAC list_ss [] >> METIS_TAC[]
  ]
) >>
CONV_TAC (RENAME_VARS_CONV ["c"]) >>
REPEAT GEN_TAC >>
ASM_SIMP_TAC (list_ss++boolSimps.LIFT_COND_ss) [PARTS_def,
  MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
Cases_on `ll` >> SIMP_TAC list_ss [] >>
rename1 `cl ++ FLAT ll' = [c:'a]` >>
Cases_on `cl` >> SIMP_TAC list_ss [] >>
SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [] >>
rename1 `(cl' = ([]:'a list)) /\ (c' = (c:'a))` >>
Cases_on `l` >> SIMP_TAC list_ss [] >> REPEAT STRIP_TAC >> (
  REPEAT BasicProvers.VAR_EQ_TAC >> FULL_SIMP_TAC list_ss [PARTS_def]
) >>
rename1 `FLAT _ = (c2:'a)::cs` >>
EQ_TAC >> STRIP_TAC >> REPEAT BasicProvers.VAR_EQ_TAC >| [
  ASM_SIMP_TAC list_ss [],

  rename1 `FLAT ll' = (_:'a)::_` >>
  Cases_on `ll'` >> FULL_SIMP_TAC list_ss [],

  Q.EXISTS_TAC `if ((cl':'a list) = []) then ll' else cl'::ll'` >>
  Cases_on `cl' = []` >> FULL_SIMP_TAC list_ss []
]);


EVAL ``parts [x;y;z]``;
EVAL ``parts [1;2]``;
EVAL ``parts [1]``;
EVAL ``parts []``;
EVAL ``parts [x;y;z;w]``;

val PARTS_EMPTY_THM = store_thm(
  "PARTS_EMPTY_THM",
  ``!e. (e =[]) = (MEM (e) (parts ([])))``,
    ASM_SIMP_TAC list_ss [PARTS_def]
);

val PARTS_EMPTY_THM2 = store_thm(
  "PARTS_EMPTY_THM2",
  ``!e. (MEM [] (parts e )) ==> (e=[])``,
     SIMP_TAC list_ss [PARTS_SPEC]
);

val PARTS_NON_EMPTY_THM = store_thm(
  "PARTS_NON_EMPTY_THM",
  ``!e x . x<>[] ==>
           (MEM x (parts e )) ==>
           (e<>[])``,
     ASM_SIMP_TAC list_ss [PARTS_EMPTY_THM]
);


val PARTS_SINGEL_THM = store_thm(
  "PARTS_SINGEL_THM",
  ``!e x. (e =[[x]]) = (MEM (e) (parts [x]))``,

    ASM_SIMP_TAC list_ss [PARTS_def]
);

val PARTS_MEM_HEAD_THM = store_thm(
  "PARTS_MEM_HEAD_THM",
  ``!h t e. (MEM e (parts t)) =
            (MEM ([h]::e) (parts (h::t)))``,
  SIMP_TAC list_ss [PARTS_SPEC]
);

val PARTS_MEM_APPEND_THM1 = store_thm(
  "PARTS_MEM_APPEND_THM1",

  ``!l1 l2 l1' l2'. (MEM l1' (parts l1))  ==>
            (MEM l2' (parts l2))  ==>
            (MEM (l1' ++ l2') (parts (l1 ++ l2)))``,

  SIMP_TAC list_ss [PARTS_SPEC]
);

val ACCEPT_def = Define
  `(accept Eps       u = (u=[]))/\
   (accept (Sym c)   u = (u=[c]))/\
   (accept (Alt p q) u = (accept p u \/ accept q u))/\
   (accept (Seq p q) u =
     (EXISTS
       (\x. accept p (FST x) /\ accept q (SND x))
       (split u)
     )
   )/\
   (accept (Rep r)   u =
        EXISTS (\partition. EVERY (\part. accept r part) partition) (parts u)
   )`;

EVAL ``accept (Sym e) [e]``;
EVAL ``accept (Sym e) []``;
EVAL ``accept (Rep (Alt (Sym 1) (Sym 2))) [6;1;2;1;1]``;
EVAL ``accept (Rep (Alt (Sym 1) (Sym 2))) [1;2;1;1]``;
EVAL ``accept (Rep (Alt (Sym 1) (Eps))) []``;
EVAL ``accept (Rep (Sym 1)) []``;
EVAL ``accept (Seq (Sym 1)(Sym 2)) [1;2]``;




(* ============================================================ *)
(*  Equaivalance of semantics and executable model         *)
(* ============================================================= *)

val FLAT_EQ_FLAT_WITHOUT_EMPTY_thm = prove(
``!words. (FLAT words) =(FLAT (FILTER (\y. []<>y) words))``,
Induct_on `words`>>
(
  ASM_SIMP_TAC (list_ss++boolSimps.LIFT_COND_ss) []
));

val LANGUAGE_ACCEPTED_THM = store_thm(
  "LANGUAGE_ACCEPTED_THM",
  ``!R x. x IN language_of R = accept R x``,
  Induct_on `R` >>
    (* Solve simple cases *)
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss) [ EXISTS_MEM,
                                                         LANGUAGE_OF_def,
                                                         ACCEPT_def]>>
    REWRITE_TAC [boolTheory.EQ_IMP_THM] >>
    REPEAT STRIP_TAC>|
  [
    (* Seq lang to accept  *)
    Q.EXISTS_TAC `(fstPrt,sndPrt)`>>
    ASM_SIMP_TAC list_ss [SPLIT_APPEND_THM]
  ,
    (* Seq accept to lang  *)
    Q.EXISTS_TAC `FST x'`>>
    Q.EXISTS_TAC `SND x'`>>
    `?l1 l2. x'=(l1,l2)` by (
      Q.EXISTS_TAC `FST x'`>>
      Q.EXISTS_TAC `SND x'`>>
      SIMP_TAC list_ss [])>>
    FULL_SIMP_TAC list_ss [SPLIT_APPEND_THM]
  ,
    (* Rep lang to accept *)
    Q.EXISTS_TAC `FILTER ($<>[]) words`>>
    FULL_SIMP_TAC list_ss [ MEM_FILTER,
                            EVERY_MEM,
                            PARTS_SPEC,
                            GSYM FLAT_EQ_FLAT_WITHOUT_EMPTY_thm ]
  ,
    (* Rep accept to lang *)
    Q.EXISTS_TAC `partition'`>>
    FULL_SIMP_TAC list_ss [ MEM_FILTER,
                            EVERY_MEM,
                            PARTS_SPEC,
                            GSYM FLAT_EQ_FLAT_WITHOUT_EMPTY_thm ]
  ]
);

 (* ======================================= *)
(*            Marked Regex               *)
 (* ======================================= *)

val MReg = Datatype `MReg = MEps
                          | MSym bool 'a
                          | MAlt MReg MReg
                          | MSeq MReg MReg
                          | MRep MReg`;

val  MARK_REG_DEF = Define
  `(MARK_REG Eps = MEps) /\
   (MARK_REG (Sym x) = MSym F x)/\
   (MARK_REG (Alt p q) = MAlt (MARK_REG p) (MARK_REG q) )/\
   (MARK_REG (Seq p q) = MSeq (MARK_REG p) (MARK_REG q) )/\
   (MARK_REG (Rep r) = MRep (MARK_REG r) )`;

val  UNMARK_REG_DEF = Define
  `(UNMARK_REG MEps = Eps) /\
   (UNMARK_REG (MSym _ x) = Sym x)/\
   (UNMARK_REG (MAlt p q) = Alt (UNMARK_REG p) (UNMARK_REG q) )/\
   (UNMARK_REG (MSeq p q) = Seq (UNMARK_REG p) (UNMARK_REG q) )/\
   (UNMARK_REG (MRep r) = Rep (UNMARK_REG r) )`;

val EMPTY_M_DEF = Define
  `
   (empty MEps = T) /\
   (empty (MSym _ _) = F) /\
   (empty (MAlt p q) = empty p \/ empty q) /\
   (empty (MSeq p q) = empty p /\ empty q) /\
   (empty (MRep _  ) = T )
  `;

EVAL ``empty MEps``;
EVAL ``empty (MAlt MEps (MSym T 2))``;
EVAL ``empty (MSeq MEps (MSym T 2))``;
EVAL ``empty (MAlt (MSym T 2) MEps)``;
EVAL ``empty (MAlt (MRep(MSym T 2)) MEps)``;
EVAL ``empty (MAlt (MRep(MSym T 2)) (MRep(MSym T 2)))``;

val FINAL_M_DEF = Define
  `(final MEps = F) /\
   (final (MSym b _) = b) /\
   (final (MAlt p q) = final p\/final q) /\
   (final (MSeq p q) = final p/\empty q \/ final q ) /\
   (final (MRep  r ) = final r )`;

EVAL ``final MEps``;
EVAL ``final (MAlt MEps (MSym T 2))``;
EVAL ``final (MSeq MEps (MSym T 2))``;
EVAL ``final (MSeq (MSym T 2) MEps)``;
EVAL ``final (MSeq (MSym T 2) MEps)``;
EVAL ``final (MSeq (MSym T 2) (MSym F 2))``;
EVAL ``final (MAlt (MRep(MSym T 2)) MEps)``;
EVAL ``final (MSeq (MRep(MSym T 2)) (MRep(MSym F 2)))``;

val SHIFT_M_DEF = Define
  `(shift _ MEps _ =  MEps )/\
   (shift m (MSym _ x) c = MSym (m /\ (x=c) ) x )/\
   (shift m (MAlt p q) c = MAlt (shift m p c) (shift m q c))/\
   (shift m (MSeq p q) c =
     MSeq (shift m p c)
          (shift (m /\ empty p \/ final p) q c))/\
   (shift m (MRep r)    c =
     MRep (shift (m \/ final r) r c) )`;

val RLANGUAGE_OF_M_DEF = Define
`  (r_language_of_m MEps =  {} )/\
   (r_language_of_m (MSym T x) = {[]} )/\
   (r_language_of_m (MSym F x) = {} ) /\
   (r_language_of_m (MAlt p q) = (r_language_of_m p) UNION (r_language_of_m q))/\
   (r_language_of_m (MSeq p q) =
     {fstPrt++sndPrt | fstPrt IN (r_language_of_m p) /\
                         sndPrt IN (language_of (UNMARK_REG q))}
       UNION
     (r_language_of_m q)
   )/\
   (r_language_of_m (MRep r)   =
     { fstPrt++sndPrt | fstPrt IN (r_language_of_m r) /\
                         sndPrt IN (language_of (UNMARK_REG (MRep r)))})`;

val LANG_OF_M_DEF = Define `langM_of m R = UNMARK_REG R`

val ACCEPT_M_DEF = Define
  `( acceptM r []      = empty r ) /\
   ( acceptM r (c::cs) = final (FOLDL (shift F) (shift T r c) cs))`;


val MARKED_M_DEF = Define
  `(marked MEps = F ) /\
   (marked (MSym v x) = v) /\
   (marked (MAlt p q) = (marked p) \/ (marked q )) /\
   (marked (MSeq p q) = (marked p) \/ (marked q )) /\
   (marked (MRep r)   = marked r )`;

(* Unmarking inverts marking,
   BUT NOT THE OTHER WAY AROUND. *)
val UNMARK_MARK_THM = store_thm(
"UNMARK_MARK_THM",
``! R. UNMARK_REG (MARK_REG R) = R``,
  Induct >> ASM_SIMP_TAC std_ss [MARK_REG_DEF, UNMARK_REG_DEF]
);

(* Right language of marked regex with no markes set is empty *)
val MARK_UNMARK_EPTY_R_LANG_THM = store_thm(
"MARK_UNMARK_EPTY_R_LANG_THM",
``!R. r_language_of_m (MARK_REG (UNMARK_REG R)) = {}``,
  Induct >>(
    ASM_SIMP_TAC (list_ss ++ pred_setSimps.PRED_SET_ss)
         [EXTENSION, RLANGUAGE_OF_M_DEF, MARK_REG_DEF, UNMARK_REG_DEF]
  )
);

(* Shifting does not affect the structure of the regex*)
val UNMARK_SHIFT_THM = store_thm(
"UNMARK_SHIFT_THM",
``!B R x. (UNMARK_REG (shift B R x)) = (UNMARK_REG R)``,
   Induct_on `R` >> FULL_SIMP_TAC list_ss [SHIFT_M_DEF, UNMARK_REG_DEF]
);

(* Not even shifting repetedly*)
val UNMARK_FOLD_SHIFT_THM = store_thm(
"UNMARK_FOLD_SHIFT_THM",
``!B R l. (UNMARK_REG (FOLDL (shift B) R l)) = (UNMARK_REG R)``,
   Induct_on `l`>>(
     FULL_SIMP_TAC list_ss [SHIFT_M_DEF, UNMARK_REG_DEF, UNMARK_SHIFT_THM]
   )
);

(* So initial language does not change ether *)
val LANG_UNMACK_SHIFT_THM = store_thm (
"LANG_UNMACK_SHIFT_THM",
``!R B h. language_of (UNMARK_REG (shift B R h)) = language_of ( UNMARK_REG R)``,
  REWRITE_TAC [UNMARK_SHIFT_THM ]
);

(* A marked regex if empty if and only if the
   empty word is in its initial language *)
val LANG_OF_EMPTY_REG_THM = store_thm (
 "LANG_OF_EMPTY_REG_THM",
 ``!R. (empty R)=([] IN language_of (UNMARK_REG R))``,
  Induct>> (
    FULL_SIMP_TAC (list_ss ++ pred_setSimps.PRED_SET_ss)
      [LANGUAGE_OF_def, UNMARK_REG_DEF, EMPTY_M_DEF]
  )>>
  Q.EXISTS_TAC `[]`>>
  ASM_SIMP_TAC (list_ss ++ pred_setSimps.PRED_SET_ss) []
);

(* epmty word is in the right language of a marked regex
   if and only if it is in a final position *)
val LANG_OF_FINAL_REG_THM = store_thm(
"LANG_OF_FINAL_REG_THM",
``!R. (final R) = [] IN r_language_of_m R``,
    Induct>>(
        Ho_Rewrite.REWRITE_TAC [boolTheory.EQ_IMP_THM, FORALL_AND_THM] >>
        STRIP_TAC >>
        (TRY (Cases_on `b`)) >> (
            FULL_SIMP_TAC (list_ss ++ pred_setSimps.PRED_SET_ss) [
                LANGUAGE_OF_def,
                UNMARK_REG_DEF,
                FINAL_M_DEF,
                RLANGUAGE_OF_M_DEF,
                LANG_OF_EMPTY_REG_THM
            ]
        )
    )>>
    STRIP_TAC>>
    Q.EXISTS_TAC `[]`>>
    FULL_SIMP_TAC (list_ss ++ pred_setSimps.PRED_SET_ss) []
);

(* An marked regex with no mark set,
   can't be in a final position     *)
val FINAL_MARK_REG_F = store_thm(
"FINAL_MARK_REG_F",
``!R. final(MARK_REG R) = F``,
  Induct >> METIS_TAC [ FINAL_M_DEF, MARK_REG_DEF]
);

(* If the right language of a marked regex is non empty,
   Then a shift with the flag set to T must have been preform on it. *)
val NON_EMPTY_RLANG_OF_UNMARKED_THM = store_thm(
"NON_EMPTY_RLANG_OF_UNMARKED_THM",
``!R B h t. t IN r_language_of_m (shift B (MARK_REG R) h) ==> (B)``,
    Induct>>(
        SIMP_TAC (list_ss ++ pred_setSimps.PRED_SET_ss) [FINAL_MARK_REG_F,SHIFT_M_DEF, RLANGUAGE_OF_M_DEF, MARK_REG_DEF]>>
        TRY (METIS_TAC [])
    )>>
    REPEAT GEN_TAC >|
    [
        Cases_on `B /\ (a=h)`>>(
            ASM_SIMP_TAC (list_ss ++ pred_setSimps.PRED_SET_ss) [RLANGUAGE_OF_M_DEF]
        )
    ,
        REPEAT STRIP_TAC>-(
        METIS_TAC[]
        )>>
        Q.PAT_X_ASSUM `!B h t. t IN r_language_of_m (shift B (MARK_REG R') h) => _`
            (fn x=> MP_TAC (Q.SPECL [`B/\empty(MARK_REG R)`, `h`, `t`] x))>>
        METIS_TAC []
    ]
);


(* If a non empty list can be partitionsed (words) such that
   a property P holds for every partition, then the list
   of partitions has a first non empty elemenet for witch the P holds.
*)
val EVERY_FLAT_FIRST_NON_EPMTY_HEAD_THM = store_thm(
"EVERY_FLAT_FIRST_NON_EPMTY_HEAD_THM",
``! words h t P. (EVERY P words) ==>
                 (FLAT words = h::t) ==>
                  (?word words'. (P (h::word)) /\ (EVERY P words') /\
                                 ((h::word) ++ (FLAT words') = h::t) )``,
    Induct>>(
         SIMP_TAC list_ss []
    )>>
    Cases_on `h`>>(
         FULL_SIMP_TAC list_ss []
    )>>
    METIS_TAC []
);


(*
  A word is in the language or a regex if and only if
  the tail of the word is in the right language of the
  marked regex with the words head positions marked.
*)
val MARK_REG_SHIFT_LANG_THM1 = store_thm(
"MARK_REG_SHIFT_LANG_THM1",
``!h t R. h::t IN language_of (R) = (t IN (r_language_of_m (shift T (MARK_REG R) h)))``,
Ho_Rewrite.REWRITE_TAC [boolTheory.EQ_IMP_THM, FORALL_AND_THM] >>
STRIP_TAC>|
[
  Induct_on `R`>> (
    REPEAT STRIP_TAC>>
    FULL_SIMP_TAC (list_ss ++ pred_setSimps.PRED_SET_ss) [SHIFT_M_DEF, RLANGUAGE_OF_M_DEF, MARK_REG_DEF, LANGUAGE_OF_def]
    )>|
  [
    Cases_on `fstPrt` >|
    [
      DISJ2_TAC>>
      FULL_SIMP_TAC list_ss []>>
      `t IN r_language_of_m (shift T (MARK_REG R') h)` by (
        METIS_TAC []
      )>>
      `empty( MARK_REG R)` by (
        ASM_SIMP_TAC std_ss [LANG_OF_EMPTY_REG_THM, UNMARK_MARK_THM]
      )>>
      ASM_SIMP_TAC list_ss []
    ,
      DISJ1_TAC>>
      Q.EXISTS_TAC `t'`>>
      Q.EXISTS_TAC `sndPrt`>>
      FULL_SIMP_TAC list_ss [UNMARK_SHIFT_THM, UNMARK_MARK_THM ]
    ]
  ,
   (*
      Mettis cant handle this for some reason,
      have to instansiate the theorem myself and ask why
  `∃word words'. ((\e.e IN language_of R) (h::word)) ∧
                (EVERY (\e.e IN language_of R) words') ∧
                (h::word ++ FLAT words' = h::t)` by METIS_TAC[EVERY_FLAT_FIRST_NON_EPMTY_HEAD_THM] *)

    MP_TAC (
      Q.SPECL [ `words`, `h`, `t`, `\e.e IN language_of R`]
              EVERY_FLAT_FIRST_NON_EPMTY_HEAD_THM
    )>>
    ASM_REWRITE_TAC []>>
    STRIP_TAC>>
    Q.EXISTS_TAC `word`>>
    Q.EXISTS_TAC `FLAT words'`>>
    FULL_SIMP_TAC (list_ss ++ pred_setSimps.PRED_SET_ss) [UNMARK_REG_DEF, UNMARK_SHIFT_THM, UNMARK_MARK_THM, LANGUAGE_OF_def]>>
    Q.EXISTS_TAC `words'`>>
    ASM_REWRITE_TAC []
  ]
,

  Induct_on `R`>>
  (
    REPEAT STRIP_TAC>>
    FULL_SIMP_TAC (list_ss ++ pred_setSimps.PRED_SET_ss) [SHIFT_M_DEF, RLANGUAGE_OF_M_DEF, MARK_REG_DEF, LANGUAGE_OF_def]
    )>|
  [
    Cases_on `a=h`>>
    FULL_SIMP_TAC (list_ss ++ pred_setSimps.PRED_SET_ss) [SHIFT_M_DEF, RLANGUAGE_OF_M_DEF, MARK_REG_DEF, LANGUAGE_OF_def]
  ,

    FULL_SIMP_TAC (list_ss ++ pred_setSimps.PRED_SET_ss) [SHIFT_M_DEF, RLANGUAGE_OF_M_DEF, MARK_REG_DEF, LANGUAGE_OF_def, UNMARK_REG_DEF, UNMARK_SHIFT_THM, UNMARK_MARK_THM, LANGUAGE_OF_def]>>
    REPEAT STRIP_TAC>>
    Q.EXISTS_TAC `h::fstPrt`>>
    Q.EXISTS_TAC `sndPrt`>>
    FULL_SIMP_TAC list_ss []
   ,

    MP_TAC (Q.SPECL [`R'`, `empty(MARK_REG R) \/ final(MARK_REG R)`, `h`, `t` ] NON_EMPTY_RLANG_OF_UNMARKED_THM)>>
    ASM_REWRITE_TAC []>>
    STRIP_TAC>|
    [
      Q.EXISTS_TAC `[]`>>
      Q.EXISTS_TAC `h::t`>>
      FULL_SIMP_TAC list_ss []>>
      ONCE_REWRITE_TAC [GSYM UNMARK_MARK_THM]>>
      METIS_TAC [ LANG_OF_EMPTY_REG_THM ]
    ,

      FULL_SIMP_TAC list_ss [FINAL_MARK_REG_F]
    ]
  ,

    FULL_SIMP_TAC (list_ss ++ pred_setSimps.PRED_SET_ss) [SHIFT_M_DEF, RLANGUAGE_OF_M_DEF, MARK_REG_DEF, LANGUAGE_OF_def, UNMARK_REG_DEF, UNMARK_SHIFT_THM, UNMARK_MARK_THM, LANGUAGE_OF_def]>>
    REPEAT STRIP_TAC>>
    Q.EXISTS_TAC `(h::fstPrt)::words`>>
    FULL_SIMP_TAC (list_ss ++ pred_setSimps.PRED_SET_ss) [SHIFT_M_DEF, RLANGUAGE_OF_M_DEF, MARK_REG_DEF, LANGUAGE_OF_def, UNMARK_REG_DEF, UNMARK_SHIFT_THM, UNMARK_MARK_THM, LANGUAGE_OF_def]
  ]
]
);


(* The language of a regex with only initila marks set,
   is a subset of the language of the same regex with
   the same initial marks set and possible other marks*)
val MARK_UNMARK_LANG_THM = store_thm(
"UNMARK_MARK_THM",
``! R t h B.  (t IN r_language_of_m (shift T (MARK_REG (UNMARK_REG R)) h)) ==>
            (t IN r_language_of_m (shift T (R) h))
``,
REWRITE_TAC [GSYM MARK_REG_SHIFT_LANG_THM1 ]>>
  Induct >> ASM_SIMP_TAC (list_ss ++ pred_setSimps.PRED_SET_ss) [ LANG_UNMACK_SHIFT_THM,LANGUAGE_OF_def,IN_UNION,RLANGUAGE_OF_M_DEF, SHIFT_M_DEF, MARK_REG_DEF, UNMARK_REG_DEF]>|
[
  REPEAT STRIP_TAC >>
  METIS_TAC []
,

  REPEAT STRIP_TAC >>
  Cases_on `fstPrt`>-(
    FULL_SIMP_TAC list_ss [LANG_OF_EMPTY_REG_THM]
  )>>
  FULL_SIMP_TAC list_ss []>>
  `t' ∈ r_language_of_m (shift T R h')` by METIS_TAC[]>>
  METIS_TAC []
,
  REPEAT STRIP_TAC >>
  MP_TAC (
        Q.SPECL [ `words`, `h`, `t`, `\e.e IN language_of (UNMARK_REG R)`]
                EVERY_FLAT_FIRST_NON_EPMTY_HEAD_THM
  )>>
  FULL_SIMP_TAC list_ss []>>
  METIS_TAC []
]);

val LANG_OF_SHIFT_MREG_THM1 = store_thm(
  "LANG_OF_SHIFT_MREG_THM1",
``!R B h t. (t IN (r_language_of_m (shift B R h))) ==>
        (h::t IN (r_language_of_m R)) \/
        (B /\ h::t IN language_of (UNMARK_REG R))``,

Induct>>
FULL_SIMP_TAC (list_ss ++ pred_setSimps.PRED_SET_ss) [SHIFT_M_DEF, RLANGUAGE_OF_M_DEF, MARK_REG_DEF, LANGUAGE_OF_def, UNMARK_REG_DEF, UNMARK_SHIFT_THM, UNMARK_MARK_THM, LANGUAGE_OF_def]>|
[
    REPEAT GEN_TAC>>
    Cases_on `b`>>
    Cases_on `B`>>
    Cases_on `a=h`>>
    ASM_SIMP_TAC list_ss [RLANGUAGE_OF_M_DEF]
,
    METIS_TAC []
,
    REPEAT STRIP_TAC>|
    [
      Cases_on `fstPrt`>> FULL_SIMP_TAC list_ss []>|
      [
         `[h] ∈ r_language_of_m R ∨ B ∧ [h] ∈ language_of (UNMARK_REG R)` by METIS_TAC []>|
         [
           DISJ1_TAC>>
           DISJ1_TAC>>
           Q.EXISTS_TAC `[h]`>>
           Q.EXISTS_TAC `sndPrt`>>
           FULL_SIMP_TAC list_ss [],

           DISJ2_TAC>>
           FULL_SIMP_TAC list_ss []>>
           Q.EXISTS_TAC `[h]`>>
           Q.EXISTS_TAC `sndPrt`>>
           FULL_SIMP_TAC list_ss []
         ],

         `h::(h'::t') ∈ r_language_of_m R ∨
          B ∧ h::(h'::t') ∈ language_of (UNMARK_REG R)` by METIS_TAC [] >|
          [
            DISJ1_TAC >>
            DISJ1_TAC >>
            Q.EXISTS_TAC `h::h'::t'`>>
            Q.EXISTS_TAC `sndPrt` >>
            FULL_SIMP_TAC list_ss [],

            DISJ2_TAC >>
            FULL_SIMP_TAC list_ss []>>
            Q.EXISTS_TAC `h::h'::t'`>>
            Q.EXISTS_TAC `sndPrt` >>
            FULL_SIMP_TAC list_ss []
          ]
       ]
    ,
      Q.PAT_X_ASSUM `! B h t. _` (fn x => MP_TAC (
               Q.SPECL [ `(B ∧ empty R ∨ final R)`, `h`, `t`] x
      ))>>
      ASM_REWRITE_TAC []>>
      STRIP_TAC>-
      (
          METIS_TAC []
      )>|
      [
         DISJ2_TAC>>
         `[] IN language_of (UNMARK_REG R)` by METIS_TAC [LANG_OF_EMPTY_REG_THM]>>
         ASM_SIMP_TAC std_ss[]>>
         Q.EXISTS_TAC `[]`>>
         Q.EXISTS_TAC `h::t`>>
         ASM_SIMP_TAC list_ss []
      ,
         DISJ1_TAC>>
         DISJ1_TAC>>
         `[] IN r_language_of_m R` by METIS_TAC [LANG_OF_FINAL_REG_THM]>>
         Q.EXISTS_TAC `[]`>>
         Q.EXISTS_TAC `h::t`>>
         ASM_SIMP_TAC list_ss []
     ]
   ]
,
     REPEAT STRIP_TAC>>
      Q.PAT_X_ASSUM `! B h t. _` (fn x => MP_TAC (
               Q.SPECL [ `(B ∨ final R)`, `h`, `fstPrt`] x
      ))>>
     ASM_REWRITE_TAC []>>
     STRIP_TAC>|
     [
       DISJ1_TAC>>
       Q.EXISTS_TAC `h::fstPrt`>>
       Q.EXISTS_TAC `sndPrt`>>
       ASM_SIMP_TAC list_ss []>>
       METIS_TAC []
     ,
       DISJ2_TAC>>
       ASM_SIMP_TAC list_ss []>>
       Q.EXISTS_TAC `(h::fstPrt)::words`>>
       ASM_SIMP_TAC list_ss []
     ,
       FULL_SIMP_TAC list_ss[]>>
       DISJ1_TAC>>
       Q.EXISTS_TAC `[]`>>
       Q.EXISTS_TAC `h::(fstPrt++sndPrt)`>>
       `[] ∈ r_language_of_m R` by METIS_TAC [ LANG_OF_FINAL_REG_THM]>>
      FULL_SIMP_TAC list_ss []>>
       Q.EXISTS_TAC `(h::fstPrt)::words`>>
       ASM_SIMP_TAC list_ss []
     ]
 ]
);

val LANG_OF_SHIFT_MREG_THM2 = store_thm(
  "LANG_OF_SHIFT_MREG_THM2",
``!R B h t. (h::t IN (r_language_of_m R)) ==> (t IN (r_language_of_m (shift B R h)))``,
Induct>>
FULL_SIMP_TAC (list_ss ++ pred_setSimps.PRED_SET_ss) [SHIFT_M_DEF, RLANGUAGE_OF_M_DEF, MARK_REG_DEF, LANGUAGE_OF_def, UNMARK_REG_DEF, UNMARK_SHIFT_THM, UNMARK_MARK_THM, LANGUAGE_OF_def]>|
[
    Cases_on `b`>>
    SIMP_TAC list_ss [RLANGUAGE_OF_M_DEF]
,
    REPEAT STRIP_TAC>> FULL_SIMP_TAC list_ss [SHIFT_M_DEF, RLANGUAGE_OF_M_DEF]
,

    REPEAT STRIP_TAC>|
    [
      Cases_on `fstPrt`>> FULL_SIMP_TAC list_ss [] >|[
        `t ∈ r_language_of_m (shift T ( R') h)` by(
            METIS_TAC [MARK_REG_SHIFT_LANG_THM1, MARK_UNMARK_LANG_THM]
        )>>
        FULL_SIMP_TAC list_ss [LANG_OF_FINAL_REG_THM]
      ,
        METIS_TAC []
      ]
    ,
      METIS_TAC []
    ]

,

    REPEAT STRIP_TAC>>
    Cases_on `fstPrt`>>
    FULL_SIMP_TAC list_ss []>|[
      MP_TAC (
        Q.SPECL [ `words`, `h`, `t`, `\e.e IN language_of (UNMARK_REG R)`]
                EVERY_FLAT_FIRST_NON_EPMTY_HEAD_THM
      )>>
      FULL_SIMP_TAC list_ss [LANG_OF_FINAL_REG_THM]>>
      REPEAT STRIP_TAC>>
      Q.EXISTS_TAC `word`>>
      Q.EXISTS_TAC `FLAT words'`>>


     `( h::(word ++ FLAT words') =   h::t) ` by METIS_TAC []>>
     FULL_SIMP_TAC list_ss [MARK_REG_SHIFT_LANG_THM1, MARK_UNMARK_LANG_THM]>>
     METIS_TAC[]
  ,

    Q.EXISTS_TAC `t'`>>
    Q.EXISTS_TAC `sndPrt`>>
    FULL_SIMP_TAC list_ss []>>
    METIS_TAC[]
  ]
]);



(* Repetedly shifting regex by a substring of
   a word in its right language puts it in a
   state such that the rest of the word is in
   its language *)
val  LANG_OF_FOLD_SHIFT_MREG_THM = store_thm (
  "LANG_OF_FOLD_SHIFT_MREG_THM",
  ``!l1 l2 R.
    l1 IN r_language_of_m (FOLDL (shift F) R l2) =
    (l2 ++ l1) IN r_language_of_m (R)``,

    Induct_on `l2`>>
    (
      SIMP_TAC list_ss [FOLDL]
    )>>
    METIS_TAC [LANG_OF_SHIFT_MREG_THM2,
               LANG_OF_SHIFT_MREG_THM1]
);

val ex_regex_def = Define
`exmpl_reg =
   MSeq
     (MRep (MSeq
         (MSeq
           (MRep (MAlt
             (MSym F 1)
             (MSym F 2)
           ))
           (MSym F 3)
         )
         (MSeq
           (MRep (MAlt
             (MSym F 1)
             (MSym F 2)
           ))
           (MSym F 3)
         )
     ))
     ((MRep (MAlt
        (MSym F 1)
        (MSym F 2)
      )))`;

EVAL ``shift T exmpl_reg 3``;
EVAL ``shift T exmpl_reg 1``;
EVAL ``shift T exmpl_reg 1``;
EVAL ``acceptM ((MRep (MAlt
        (MSym F 1)
        (MSym F 2)
      ))) []``;
EVAL ``acceptM exmpl_reg [1;3;2;1;2;3;1]``;
EVAL ``acceptM ((MRep (MAlt
        (MSym F 1)
        (MSym F 2)
      ))) [1;2;1;1;1;1;1]``;
EVAL ``acceptM ((MRep (MSeq
        (MSym F 1)
        (MSym F 2)
      ))) [1;2;1;2]``;
EVAL ``acceptM (MSym T 1) [1]``;


(*******************************************)
(* acceptM of marked regex accepts    *)
(* exactly thoughts words in the      *)
(* langugae of the unmarked regex     *)
(*******************************************)
val ACCEPT_M_LANGUAGE_THM = store_thm (
"ACCEPT_M_LANGUAGE_THM",
``!r w. acceptM (MARK_REG r) w <=> w IN (language_of r)``,
  REPEAT STRIP_TAC >>
  Cases_on `w`>>(
     SIMP_TAC list_ss [
     ACCEPT_M_DEF,
     LANG_OF_EMPTY_REG_THM,
     UNMARK_MARK_THM,
     LANG_OF_FINAL_REG_THM,
     MARK_REG_SHIFT_LANG_THM1,
     LANG_OF_FOLD_SHIFT_MREG_THM]
  )
);

 (* ======================================= *)
(*            Code generation            *)
 (* ======================================= *)


emitML (!Globals.emitMLDir) ("poregex", [
                         MLSIG "Type 'a list = 'a listML.list",
                         OPEN ["list"],
                         DATATYPE `Reg = Eps
                                       | Sym 'a
                                       | Alt Reg Reg
                                       | Seq Reg Reg
                                       | Rep Reg`,
                         DEFN SPLIT_def,
                         DEFN PARTS_def,
                         DEFN ACCEPT_def
                           ]);
val _ = export_theory();
