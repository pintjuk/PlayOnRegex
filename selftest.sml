open List
open Random
open regexpML
open regexp
open Benchmark
open regexpMatch

val gen = Random.newgenseed 10.0;

fun symbol x = Symbs (pred_to_set (fn y => (y = x) ))

fun toHolRegex  Eps  = Epsilon
    | toHolRegex  (Sym c) = symbol c
    | toHolRegex  (Alt (a, b)) = Sum (toHolRegex a, toHolRegex b )
    | toHolRegex  (Seq (a, b)) = Dot (toHolRegex a, toHolRegex b )
    | toHolRegex  (Rep (r)) = Star (toHolRegex r)

fun smatch_dfa     r l = match (toHolRegex r) l

(*
*    (a|eps)^n(a)^n
*)
fun testreg1  n = Seq(
        rep_n (Alt( Sym #"a", Eps)) n,
        rep_n (Sym #"a") n);

(* regex that maches a string with even number of c's
* ( language : {a, b,c} )
*
*       ((a|b)*c(a|b)*c)*(a|b)*
*)
val evenNumOfCs = let
    val nocs = Rep (Alt((Sym #"a"), (Sym #"b")));
    val onec = Seq (nocs, (Sym #"c"));
in
        Seq ((Rep (Seq (onec, onec))), nocs)
end

fun regresion_test ( reg, string) =let
    val oracle = (smatch_dfa reg string)
    val mark_res = smatch_mark reg string
    val nonmark_res = smatch_nonmark reg string
in
(
    if oracle <> mark_res then
        print   ("\n(*** FAILURE ***)\n" ^
                "marked regex answared: " ^ (Bool.toString mark_res) ^
                "\ncase: " ^string ^
                "\nexpected: " ^ (Bool.toString oracle) ^ "\n")
    else ();
    if oracle <> nonmark_res then
        print   ("\n(*** FAILURE ***)\n" ^
                "nonmarked regex answared: " ^ (Bool.toString nonmark_res) ^
                "\ncase: " ^string ^
                "\nexpected: " ^ (Bool.toString oracle) ^ "\n")
    else ();
    oracle = mark_res andalso oracle=mark_res
)
end


fun runTests tests =
    if (all (fn x=> (x())) (tests ))
    then (OS.Process.exit OS.Process.success)
    else (OS.Process.exit OS.Process.failure)


fun timeTest (matcher, expected, reg, string) = let
    val t = ref Time.zeroTime;
    val r = ref false;
in(
    restart();
    r := matcher reg string;
    t:= (#usr  (time()))+(#sys  (time()));
    stop();
    (* return: *)
    {   time   = !t,
        result = (expected = (!r))
    }
)end

fun scaleTest (matcher, tests) =
    foldl (fn ({n, expected, reg, string}, {nofails, line})=>
        let val tt_out = timeTest (matcher,
                                    expected,
                                    reg,
                                    string)
        in(
            if not (#result tt_out) then print "***FAILURE***\n" else ();
            {nofails= (#result tt_out) andalso nofails,
             line= line^((Int.toString n)^ ": " ^
                   (Time.toString (#time tt_out)) ^ "\n")}
        )
        end
    ) {nofails=true, line=""} tests

fun makeNtests (from, to, step) = if from < to
then {n=from, expected=true,
      reg=testreg1 from,
      string = rep_string_n "a" from }::makeNtests(from+step, to, step)
else []

fun makeNtests2 (from, to, step) = let
    val ABs =  (map ( fn x => nth ([#"a", #"b", #"c"], x))
                                     (rangelist (0, 3) (from, gen)))
in
    if from < to
    then {
            n=from,
            expected= (((length( filter (fn x=> (x = #"c")) (ABs))) mod 2 )=0),
            reg=evenNumOfCs,
            string = (String.implode ABs)
         }::makeNtests2(from+step, to, step)
    else []
end

fun performance ()= let
val res = ref false
in
(
  start();
  res := smatch_mark (testreg1 200) ((rep_string_n "a" 200));
  stopAndPrint "test result";
  !res
)
end

val n_max=130;
val n_max2=300000;
val num_regre_tests=40;
runTests
[
    fn ()=>(
        print ("Runing regresion tests against regexpMatch.sml\n"^
         "using regex:  ((a|b)*c(a|b)*c)*(a|b)*");
        if all (fn x=>x)
               ( ((map (fn x=> regresion_test (evenNumOfCs,x) )) o
                (map (fn x=> String.implode (map ( fn x => nth ([#"a", #"b", #"c"], x))
                                    (rangelist (0, 3) (x, gen))))))
                (rangelist (3,20) (num_regre_tests, gen)))
        then (print ("Succesfully ran "^
                     (Int.toString num_regre_tests)^
                     " cases!\n");
              true)
        else (print "FAILURE!\n"; false)
    ),
    fn ()=>let
        val outcome = scaleTest (smatch_dfa, makeNtests (1, n_max, 10))
    in(
        print ("\n  Scaleability tests1:\n"^
                 "  ===================\n"^
               "\n  (regexpMatch.sml):\n"^
                 "  ------------------\n"^
              "matching (a|eps)^n(a)^n  against  a^n\n"^
              "n: time(s)\n" ^ (#line outcome));
        (#nofails outcome)
    )end,
    fn ()=>let
        val outcome = scaleTest (smatch_mark, makeNtests (1, n_max, 10))
    in(
        print ("\n  Marked regex implementation:\n"^
                 "  ---------------------------\n"^
              "matching (a|eps)^n(a)^n  against  a^n\n"^
              "\nn: time(s)\n" ^ (#line outcome));
        (#nofails outcome)
    )end,
    fn ()=>let
        val outcome = scaleTest (smatch_nonmark, makeNtests (1, n_max, 10))
    in(
        print ("\n  Non Marked regex implementation:\n"^
                 "  --------------------------------\n"^
              "  matching (a|eps)^n(a)^n  against  a^n\n"^
              "\nn: time(s)\n" ^ (#line outcome));
        (#nofails outcome)
    )end,
    fn ()=>let
        val outcome = scaleTest (smatch_dfa, makeNtests2 (6, n_max2, 20000))
    in(
        print ("\n  Scaleability tests 2:\n"^
                 "  =====================\n"^
               "\n  (regexpMatch.sml):\n"^
                 "  ------------------\n"^
              "  matching ((a|b)*c(a|b)*c)*(a|b)*\n  against  string of length n \n"^
              "n: time(s)\n" ^ (#line outcome));
        (#nofails outcome)
    )end,
    fn ()=>let
        val outcome = scaleTest (smatch_mark, makeNtests2 (6, n_max2, 20000))
    in(
        print ("\n  Marked regex implementation:\n"^
                 "  ---------------------------\n"^
              "  matching ((a|b)*c(a|b)*c)*(a|b)*\n  against  string of length n \n"^
              "\nn: time(s)\n" ^ (#line outcome));
        (#nofails outcome)
    )end,
    fn ()=>let
        val outcome = scaleTest (smatch_nonmark, makeNtests2 (1, 25, 5))
    in(
        print ("\n  Non Marked regex implementation:\n"^
                 "  --------------------------------\n"^
              "  matching ((a|b)*c(a|b)*c)*(a|b)*\n  against  string of length n \n"^
              "\nn: time(s)\n" ^ (#line outcome));
        (#nofails outcome)
    )end
]
