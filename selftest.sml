open listML
open regexpML
val _ = print (FOLDL (fn x => fn y => x ^ ", "^ y ) "" [ "aeou", "1234"]);
(*val _ = OS.Process.exit OS.Process.failure;
val _ = OS.Process.exit OS.Process.success;*)
