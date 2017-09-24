structure regexp :> regexp =
struct
    open listML
    open regexpML
    open regexpMatch
    open Benchmark
    open Random
    open List

    (* use string to define a sequanse of symbols *)
    fun op$ w =
        let
            val charlist      = String.explode w;
            val seqBuilder    = (fn x => fn y => Seq (x ,(Sym y)));
        in
            FOLDL seqBuilder (Sym (HD charlist)) (TL charlist)
        end

    fun rep_n R 0 = raise Domain
      | rep_n R 1 = R
      | rep_n R n = Seq (R, rep_n R (n-1))

    fun rep_string_n s 0 = ""
      | rep_string_n s n = s ^ (rep_string_n s (n-1))


    (* general match *)
    fun match_mark r l = accept_m (mark r) l
    fun match_nonmark r l = accept r l
    (* and to make it easear to work with strings *)
    fun smatch_mark r l = accept_m (mark r) (String.explode l)
    fun smatch_nonmark r l = accept  r (String.explode l)
end
