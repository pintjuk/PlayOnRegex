structure regexp :> regexp =
struct
    open listML
    open regexpML

    (* use string to define a sequanse of symbols *)
    val ! = (fn w =>
        let
            val charlist      = String.explode w;
            val seqBuilder    = (fn x => fn y => Seq (x ,(Sym y)));
        in
            FOLDL seqBuilder (Sym (HD charlist)) (TL charlist)
        end
    );

    (* better syntax for regex *)
    val * = (fn (x, y) => Seq(x,y));
    val + = (fn (x, y) => Alt(x,y));
    val r = (fn x =>  Rep(x));


    (* general match *)
    fun match r l = accept_m (mark r) l
    fun match_nonmark r l = accept r l
    (* and to make it easear to work with strings *)
    fun smatch r l = accept_m (mark r) (String.explode l)
    fun smatch_nonmark r l = accept  r (String.explode l)
end
