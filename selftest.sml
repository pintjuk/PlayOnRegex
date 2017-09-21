open listML
open regexpML
val _ = print (FOLDL (fn x=>fn y => x ^ ", "^ y ) "" [ "aeou", "1234"]);
