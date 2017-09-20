open HolKernel Parse boolLib bossLib
open pred_setSyntax pred_setLib listTheory rich_listTheory listTheory pred_setTheory arithmeticTheory
open EmitML basis_emitTheory

val _ = new_theory "regexp"

(* =========================== *)
(*    DEFINITION OF REGEX    *)
(* =========================== *)
val Q_Regex = `Reg = Eps
                   | Sym 'a
                   | Alt Reg Reg
                   | Seq Reg Reg
                   | Rep Reg`

val Regex = Datatype Q_Regex;

(* =========================== *)
(*    REGEX Semantix         *)
(* =========================== *)

val language_of_def = Define
  `(language_of Eps = {[]}) /\
   (language_of (Sym c) = {[c]}) /\
   (language_of (Alt a b) = (language_of a) UNION (language_of b) ) /\
   (language_of (Seq f s) =
     {fstPrt ++ sndPrt | (fstPrt IN language_of f) /\
                         (sndPrt IN language_of s) } ) /\
   (language_of (Rep r) =
     {x| ?words. (EVERY (\e. e IN language_of r) words) /\
                 ((FLAT words)=x)})`;

val FLAT_EQ_FLAT_WITHOUT_EMPTY_THM = prove(
``!words. (FLAT (FILTER (\y. []<>y) words))= (FLAT words) ``,
Induct_on `words`>>
(
  ASM_SIMP_TAC (list_ss++boolSimps.LIFT_COND_ss) []
));


val LANGUAGE_OF_REWRITE_THM = store_thm (
"LANGUAGE_OF_REWRITE_THM",
 ``(!w. w     IN (language_of Eps) <=> (w= [])) /\
   (!w c. w   IN (language_of (Sym c)) <=> (w =[c])) /\
   (!w a b. w IN language_of (Alt a b) <=> (w IN language_of a) \/
                                         (w IN language_of b) ) /\
   (!w f s. w IN (language_of (Seq f s)) <=>
       ?fstPrt sndPrt. (w=fstPrt++sndPrt)/\
       fstPrt IN language_of f /\
       sndPrt IN language_of s )/\
   (!w r . w IN language_of (Rep r) =
     ?words.
     EVERY (\e. e IN language_of r) words /\
     ((FLAT  words)=w))``,

    SIMP_TAC (std_ss ++ pred_setSimps.PRED_SET_ss) [language_of_def]
);

val LANGUAGE_OF_REWRITE_THM_NO_NIL = store_thm (
"LANGUAGE_OF_REWRITE_THM_NO_NIL",
 ``(!w. w     IN (language_of Eps) <=> (w= [])) /\
   (!w c. w   IN (language_of (Sym c)) <=> (w =[c])) /\
   (!w a b. w IN language_of (Alt a b) <=> (w IN language_of a) \/
                                         (w IN language_of b) ) /\
   (!w f s. w IN (language_of (Seq f s)) <=>
       ?fstPrt sndPrt. (w=fstPrt++sndPrt)/\
       fstPrt IN language_of f /\
       sndPrt IN language_of s )/\
   (!w r . w IN language_of (Rep r) =
     ?words. ~(MEM [] words) /\
     EVERY (\e. e IN language_of r) words /\
     ((FLAT  words)=w))``,

    SIMP_TAC (std_ss ++ pred_setSimps.PRED_SET_ss) [language_of_def]>>
    REPEAT GEN_TAC>>
    Tactical.REVERSE EQ_TAC >- (
        METIS_TAC []
    )>>
    STRIP_TAC>>
    Q.EXISTS_TAC `FILTER ($<>[]) words`>>
    FULL_SIMP_TAC list_ss [MEM_FILTER, EVERY_MEM, FLAT_EQ_FLAT_WITHOUT_EMPTY_THM]
);

val SanityRep = prove(
  ``[1;2;1;1] IN language_of (Rep (Alt (Sym 1) (Sym 2)))``,
  Ho_Rewrite.REWRITE_TAC [language_of_def,IN_GSPEC_IFF]>>
  Q.EXISTS_TAC `[[1];[2];[1];[1]]` >>
  SIMP_TAC list_ss []
);

val SanitySeq1 = prove(
  ``[1;2] IN language_of (Seq (Sym 1)(Sym 2))``,
  Ho_Rewrite.REWRITE_TAC [language_of_def,IN_GSPEC_IFF]>>
  REWRITE_TAC [
    SET_SPEC_CONV
      ``[1; 2] IN {fstPrt ++ sndPrt | fstPrt IN {[1]} /\ sndPrt IN {[2]}}``
  ]>>
  SIMP_TAC list_ss []
);

val AND_FOLD_FALSE_THM = prove(
  ``!a. ~(FOLDL $/\ F a)``,
  Induct >> ASM_SIMP_TAC std_ss [FOLDL]
);

val sanity_rep_nullable_thm = prove(
  ``([] IN language_of (Rep (Alt (Sym 1) (Sym 2))))``,
  Ho_Rewrite.REWRITE_TAC [language_of_def,IN_GSPEC_IFF, NOT_EXISTS_THM]>>
  Q.EXISTS_TAC `[]`>>
  SIMP_TAC list_ss []
);

val sanity_rep_nullable_thm = prove(
  ``!R. ([] IN language_of (Rep R))``,
  Induct>>
  Ho_Rewrite.REWRITE_TAC [language_of_def,IN_GSPEC_IFF]>>
  TRY STRIP_TAC>>
  Q.EXISTS_TAC `[]`>>
  SIMP_TAC (list_ss) []
);

(* =========================== *)
(* Executable model of regex *)
(* =========================== *)

val split_def = Define
  `(split []    = [([],[])]) /\
   (split (c::cs) = ([],c::cs)::(MAP (\x. (c::(FST x), SND x)) (split cs)))`;

val MEM_SPLIT_APPEND_THM = store_thm(
  "MEM_SPLIT_APPEND_THM",
  ``!A B. MEM (A,B) (split (A++B))``,

Induct >| [
  Cases >> SIMP_TAC list_ss [split_def],
  ASM_SIMP_TAC (list_ss++QI_ss) [split_def, MEM_MAP]
]);



val SPLIT_APPEND_THM =  store_thm(
  "SPLIT_APPEND_THM",
  ``!l l1 l2. (MEM (l1, l2) (split l)) <=> (l1 ++ l2 = l)``,
  SIMP_TAC std_ss [boolTheory.EQ_IMP_THM, FORALL_AND_THM] >>
  (Tactical.REVERSE CONJ_TAC) >-(
    Induct >- (
      Cases >> SIMP_TAC list_ss [split_def]
    )>>
    ASM_SIMP_TAC (list_ss++QI_ss) [split_def, MEM_MAP]
  )>>
  Induct>-(
     ASM_SIMP_TAC (list_ss) [split_def]
  )>>

  ASM_SIMP_TAC (list_ss) [split_def, MEM_MAP]>>
  REPEAT STRIP_TAC>>
  FULL_SIMP_TAC list_ss []
);



(* It was pritty hard to work with this definition,
   maybe i should redefine this  *)
val parts_def = Define
  `(parts []     = [[]]) /\
   (parts (c::cs) =
     if cs = []
     then [[[c]]]
     else FLAT (MAP (\x. [[c]::x; (c::(HD x))::(TL x)]) (parts cs)))
   `;

val PARTS_SPEC = store_thm ("PARTS_SPEC",
  ``!(l:'a list) ll. MEM ll (parts l) <=> (~(MEM [] ll) /\ (FLAT ll = l))``,
Induct >- (
  SIMP_TAC list_ss [parts_def, FLAT_EQ_NIL, EVERY_MEM] >>
  Cases_on `ll` >| [
    SIMP_TAC list_ss [],

    SIMP_TAC list_ss [] >> METIS_TAC[]
  ]
) >>
CONV_TAC (RENAME_VARS_CONV ["c"]) >>
REPEAT GEN_TAC >>
ASM_SIMP_TAC (list_ss++boolSimps.LIFT_COND_ss) [parts_def,
  MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
Cases_on `ll` >> SIMP_TAC list_ss [] >>
rename1 `cl ++ FLAT ll' = [c:'a]` >>
Cases_on `cl` >> SIMP_TAC list_ss [] >>
SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [] >>
rename1 `(cl' = ([]:'a list)) /\ (c' = (c:'a))` >>
Cases_on `l` >> SIMP_TAC list_ss [] >> REPEAT STRIP_TAC >> (
  REPEAT BasicProvers.VAR_EQ_TAC >> FULL_SIMP_TAC list_ss [parts_def]
) >>
rename1 `FLAT _ = (c2:'a)::cs` >>
EQ_TAC >> STRIP_TAC >> REPEAT BasicProvers.VAR_EQ_TAC >| [
  ASM_SIMP_TAC list_ss [],

  rename1 `FLAT ll' = (_:'a)::_` >>
  Cases_on `ll'` >> FULL_SIMP_TAC list_ss [],

  Q.EXISTS_TAC `if ((cl':'a list) = []) then ll' else cl'::ll'` >>
  Cases_on `cl' = []` >> FULL_SIMP_TAC list_ss []
]);

val PARTS_EMPTY_THM = store_thm(
  "PARTS_EMPTY_THM",
  ``!e. (e =[]) = (MEM (e) (parts ([])))``,
    ASM_SIMP_TAC list_ss [parts_def]
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


val PARTS_SINGLE_THM = store_thm(
  "PARTS_SINGLE_THM",
  ``!e x. (e =[[x]]) = (MEM (e) (parts [x]))``,

    ASM_SIMP_TAC list_ss [parts_def]
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

val accept_def = Define
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





(* ============================================================ *)
(*  Equaivalance of semantics and executable model         *)
(* ============================================================= *)


val LANGUAGE_ACCEPTED_THM = store_thm(
  "LANGUAGE_ACCEPTED_THM",
  ``!R x. x IN language_of R = accept R x``,

  Induct_on `R` >> (
            ASM_SIMP_TAC std_ss [LANGUAGE_OF_REWRITE_THM_NO_NIL, accept_def, EXISTS_MEM, SPLIT_APPEND_THM, pairTheory.EXISTS_PROD, PARTS_SPEC] >>
            METIS_TAC[]
  ));


 (* ======================================= *)
(*            Marked Regex               *)
 (* ======================================= *)
val Q_MReg = `MReg = MEps
                          | MSym bool 'a
                          | MAlt MReg MReg
                          | MSeq MReg MReg
                          | MRep MReg`;

val MReg = Datatype Q_MReg;

val  mark_def = Define
  `(mark Eps = MEps) /\
   (mark (Sym x) = MSym F x)/\
   (mark (Alt p q) = MAlt (mark p) (mark q) )/\
   (mark (Seq p q) = MSeq (mark p) (mark q) )/\
   (mark (Rep r) = MRep (mark r) )`;

val  unmark_def = Define
  `(unmark MEps = Eps) /\
   (unmark (MSym _ x) = Sym x)/\
   (unmark (MAlt p q) = Alt (unmark p) (unmark q) )/\
   (unmark (MSeq p q) = Seq (unmark p) (unmark q) )/\
   (unmark (MRep r) = Rep (unmark r) )`;

val empty_def = Define
  `
   (empty MEps = T) /\
   (empty (MSym _ _) = F) /\
   (empty (MAlt p q) = empty p \/ empty q) /\
   (empty (MSeq p q) = empty p /\ empty q) /\
   (empty (MRep _  ) = T )
  `;


val final_def = Define
  `(final MEps = F) /\
   (final (MSym b _) = b) /\
   (final (MAlt p q) = final p\/final q) /\
   (final (MSeq p q) = final p/\empty q \/ final q ) /\
   (final (MRep  r ) = final r )`;

val shift_def = Define
  `(shift _ MEps _ =  MEps )/\
   (shift m (MSym _ x) c = MSym (m /\ (x=c) ) x )/\
   (shift m (MAlt p q) c = MAlt (shift m p c) (shift m q c))/\
   (shift m (MSeq p q) c =
     MSeq (shift m p c)
          (shift (m /\ empty p \/ final p) q c))/\
   (shift m (MRep r)    c =
     MRep (shift (m \/ final r) r c) )`;

val r_language_of_m_def = Define
`  (r_language_of_m MEps =  {} )/\
   (r_language_of_m (MSym B x) = if B then {[]} else {} )/\
   (r_language_of_m (MAlt p q) = (r_language_of_m p) UNION (r_language_of_m q))/\
   (r_language_of_m (MSeq p q) =
     {fstPrt++sndPrt | fstPrt IN (r_language_of_m p) /\
                         sndPrt IN (language_of (unmark q))}
       UNION
     (r_language_of_m q)
   )/\
   (r_language_of_m (MRep r)   =
     { fstPrt++sndPrt | fstPrt IN (r_language_of_m r) /\
                         sndPrt IN (language_of (unmark (MRep r)))})`;

val accept_m_def = Define
  `( accept_m r []      = empty r ) /\
   ( accept_m r (c::cs) = final (FOLDL (shift F) (shift T r c) cs))`;


(* TT: suggested alternative. Acually the rewrite lemma is useful already before and
       should come shortly after the definition. *)
val IN_R_LANGUAGE_OF_M = store_thm ("IN_R_LANGUAGE_OF_M",
`` (!w. ~(w IN r_language_of_m MEps)) /\
   (!w b x. w IN (r_language_of_m (MSym b x)) <=> (w = []) /\ b) /\
   (!w p q. w IN r_language_of_m (MAlt p q) <=>
        (w IN (r_language_of_m p)) \/ w IN (r_language_of_m q)) /\
   (!w p q. w IN r_language_of_m (MSeq p q) <=>
       (w IN r_language_of_m q) \/
       (?w1 w2. (w = w1 ++ w2) /\ (w1 IN (r_language_of_m p)) /\
                (w2 IN (language_of (unmark q))))) /\
   (!w r. w IN r_language_of_m (MRep r) <=>
          ?w1 w2. (w = w1 ++ w2) /\
                  (w1 IN (r_language_of_m r) /\
                   w2 IN (language_of (Rep (unmark r)))))``,

SIMP_TAC ( std_ss++
           pred_setSimps.PRED_SET_ss++
           boolSimps.EQUIV_EXTRACT_ss++
           boolSimps.LIFT_COND_ss)
         [ r_language_of_m_def, unmark_def]
(* TT: This case split disappears, if you use a different definition.
REPEAT STRIP_TAC >> Cases_on `b` >> (
  SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [r_language_of_m_def]
)*)
);

(* A marked regex empty if and only if the
   empty word is in its initial language *)
val LANG_OF_EMPTY_REG_THM = store_thm (
 "LANG_OF_EMPTY_REG_THM",
 ``!R. (empty R)=([] IN language_of (unmark R))``,
  Induct>> (
    FULL_SIMP_TAC (list_ss ++ pred_setSimps.PRED_SET_ss)
      [LANGUAGE_OF_REWRITE_THM, unmark_def, empty_def]
  )>>
  Q.EXISTS_TAC `[]`>>
  ASM_SIMP_TAC (list_ss ++ pred_setSimps.PRED_SET_ss) []
);

val LANG_OF_FINAL_REG_THM = store_thm(
"LANG_OF_FINAL_REG_THM",
``!R. (final R) = [] IN r_language_of_m R``,
    Induct >> (
      ASM_SIMP_TAC (list_ss++boolSimps.EQUIV_EXTRACT_ss)
                   [IN_R_LANGUAGE_OF_M, final_def,
                    LANG_OF_EMPTY_REG_THM, sanity_rep_nullable_thm]
    )
);

(* Unmarking inverts marking,
   BUT NOT THE OTHER WAY AROUND. *)
val UNMARK_MARK_THM = store_thm(
"UNMARK_MARK_THM",
``! R. unmark (mark R) = R``,
  Induct >> ASM_SIMP_TAC std_ss [mark_def, unmark_def]
);

(* Right language of marked regex with no markes set is empty *)
val NO_MARKS_EMPTY_R_LANG_THM = store_thm(
"NO_MARKS_EMPTY_R_LANG_THM",
``!R. r_language_of_m (mark R) = {}``,
  Induct >>(
    ASM_SIMP_TAC (list_ss ++ pred_setSimps.PRED_SET_ss)
         [EXTENSION, IN_R_LANGUAGE_OF_M, mark_def]
  )
);

(* Shifting does not affect the structure of the regex*)
val UNMARK_SHIFT_THM = store_thm(
"UNMARK_SHIFT_THM",
``!B R x. (unmark (shift B R x)) = (unmark R)``,
   Induct_on `R` >> FULL_SIMP_TAC list_ss [shift_def, unmark_def]
);

val LANG_OF_SHIFT = prove(
`` !R B h t.
     t IN r_language_of_m (shift B R h) =
     h::t IN r_language_of_m R \/ B /\ h::t IN language_of (unmark R)``,

    Induct >>(
        FULL_SIMP_TAC (list_ss++boolSimps.EQUIV_EXTRACT_ss)
                    [ PULL_EXISTS, UNMARK_SHIFT_THM, shift_def, IN_R_LANGUAGE_OF_M,
                        LANGUAGE_OF_REWRITE_THM_NO_NIL, unmark_def,
                        LANG_OF_EMPTY_REG_THM, LANG_OF_FINAL_REG_THM])>|[
        (* Seq case: *)
        REPEAT STRIP_TAC>>
        EQ_TAC>-(
            METIS_TAC [APPEND]
        )>>
        STRIP_TAC>>(
            rename1 `h::t = w1++w2` >>
            Cases_on `w1`>>(
                FULL_SIMP_TAC list_ss []
            )>>
            METIS_TAC [APPEND]
        ),

        (* Rep case: *)
        REPEAT STRIP_TAC>>
        EQ_TAC>|[
            REPEAT STRIP_TAC>-(
                METIS_TAC [APPEND]
            )>>
            rename1 `t = w1++FLAT words` >>
            rename1 `h::w1 IN language_of(unmark R)` >|
            [
                DISJ2_TAC>>
                Q.EXISTS_TAC `(h::w1)::words`>>
                ASM_SIMP_TAC list_ss [],

                rename1 `t = w1++FLAT words` >>
                rename1 `h::w1 IN language_of(unmark R)` >>
                DISJ1_TAC>>
                Q.EXISTS_TAC `[]`>>
                Q.EXISTS_TAC `(h::w1)::words`>>
                FULL_SIMP_TAC list_ss []
            ],

            REPEAT STRIP_TAC>|[
                (* When w1=[] in the fist case then
                   the following cases are equal *)
                rename1 `h::t = w1++FLAT words` >>
                Tactical.REVERSE(Cases_on `w1`) >- (
                    Q.EXISTS_TAC `t'`>>
                    Q.EXISTS_TAC `words`>>
                    FULL_SIMP_TAC list_ss []
                )>>
                FULL_SIMP_TAC list_ss []>>
                `?c1 c2. words = (h::c1)::c2` by (
                    Cases_on `words`>>
                    FULL_SIMP_TAC list_ss []>>
                    Cases_on `h'`>>
                    FULL_SIMP_TAC list_ss []
                )>>
                Q.EXISTS_TAC `c1`>>
                Q.EXISTS_TAC `c2`>>
                FULL_SIMP_TAC list_ss [],

                `?c1 c2. words = (h::c1)::c2` by (
                    Cases_on `words`>>
                    FULL_SIMP_TAC list_ss []>>
                    Cases_on `h'`>>
                    FULL_SIMP_TAC list_ss []
                )>>
                Q.EXISTS_TAC `c1`>>
                Q.EXISTS_TAC `c2`>>
                FULL_SIMP_TAC list_ss []

           ]
        ]
]);


(* Repetedly shifting regex by a substring of
   a word in its right language puts it in a
   state that has rest of the word is in
   its right language *)
val  LANG_OF_FOLD_SHIFT = store_thm (
  "LANG_OF_FOLD_SHIFT",
  ``!l1 l2 R.
    l1 IN r_language_of_m (FOLDL (shift F) R l2) =
    (l2 ++ l1) IN r_language_of_m (R)``,

    Induct_on `l2`>>
    (
      SIMP_TAC list_ss [FOLDL]
    )>>
    METIS_TAC[ LANG_OF_SHIFT ]
);

(*******************************************)
(* accept_m of marked regex accepts    *)
(* exactly thoughts words in the      *)
(* langugae of the unmarked regex     *)
(*******************************************)



val ACCEPT_M_LANGUAGE_THM = store_thm (
"ACCEPT_M_LANGUAGE_THM",
``!r w. accept_m (mark r) w <=> w IN (language_of r)``,
  REPEAT STRIP_TAC >>
  Cases_on `w`>>(
     SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss)
        [LANG_OF_SHIFT ,
         NO_MARKS_EMPTY_R_LANG_THM,
         LANG_OF_FOLD_SHIFT,
         accept_m_def,
         LANG_OF_EMPTY_REG_THM,
         UNMARK_MARK_THM,
         LANG_OF_FINAL_REG_THM
   ])
);

 (* ======================================= *)
(*            Code generation            *)
 (* ======================================= *)

emitML (!Globals.emitMLDir) ("poregex", [
                         MLSIG "Type 'a list = 'a listML.list",
                         OPEN ["list"],
                         DATATYPE Q_Regex,
                         DEFN split_def,
                         DEFN parts_def,
                         DEFN accept_def
                           ]);
val _ = export_theory();
