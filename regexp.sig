signature regexp =
sig
    val $ : string -> char regexpML.Reg
    val rep_n : 'a regexpML.Reg -> int -> 'a regexpML.Reg
    val rep_string_n: string -> int -> string
    val match_mark : ''a regexpML.Reg -> ''a list -> bool
    val match_nonmark : ''a regexpML.Reg -> ''a list -> bool
    val smatch_mark : char regexpML.Reg -> string -> bool
    val smatch_nonmark : char regexpML.Reg -> string -> bool
end
