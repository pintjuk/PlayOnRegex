signature regexp =
sig
    val ! : string -> char regexpML.Reg
    val * : 'a regexpML.Reg * 'a regexpML.Reg -> 'a regexpML.Reg
    val + : 'a regexpML.Reg * 'a regexpML.Reg -> 'a regexpML.Reg
    val r : 'a regexpML.Reg -> 'a regexpML.Reg
    val match : ''a regexpML.Reg -> ''a list -> bool
    val match_nonmark : ''a regexpML.Reg -> ''a list -> bool
    val smatch : char regexpML.Reg -> string -> bool
    val smatch_nonmark : char regexpML.Reg -> string -> bool
end
