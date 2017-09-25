signature regexp =
sig
    (* String into a regex that matches the sequence of thous characters *)
    val $ : string -> char regexpML.Reg
    (* Repeat regex n times *)
    val rep_n : 'a regexpML.Reg -> int -> 'a regexpML.Reg
    (* Repeat a string n times *)
    val rep_string_n: string -> int -> string
    (* Match using marked regex on list of arbitrary elements *)
    val match_mark : ''a regexpML.Reg -> ''a list -> bool
    (* Match using list spiting on list of arbitrary elements *)
    val match_nonmark : ''a regexpML.Reg -> ''a list -> bool
    (* Match using marked regex on strings *)
    val smatch_mark : char regexpML.Reg -> string -> bool
    (* Match using list splitting on strings *)
    val smatch_nonmark : char regexpML.Reg -> string -> bool
end
