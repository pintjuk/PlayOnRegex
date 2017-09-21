open listML
open regexpML
open regexp

fun test_reg (comment, backend, expected, reg, string) =
    if ((backend reg string) = expected)
    then let
	val _ = print ("SUCCESS: " ^ comment ^ "\n")
    in true end
    else let
        val _ =print ("FAULUR: " ^ comment ^ "\n")
    in false end;

fun runTests tests =
    if (EVERY (fn x=> x) (map test_reg tests ))
    then (OS.Process.exit OS.Process.success)
    else (OS.Process.exit OS.Process.failure);
val _ = runTests [
    ("test 1", smatch ,false, ( r (!"a"* !"b" + !"ce")), "cea"),
    ("test 2", smatch ,true, ( r (!"a"* !"b" + !"ce")), "ceceabab")
];
