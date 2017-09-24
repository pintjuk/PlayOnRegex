signature regexpML =
sig
  datatype 'a Reg
       = Eps
       | Sym of 'a
       | Alt of 'a Reg * 'a Reg
       | Seq of 'a Reg * 'a Reg
       | Rep of 'a Reg
  datatype 'a MReg
       = MEps
       | MSym of bool * 'a
       | MAlt of 'a MReg * 'a MReg
       | MSeq of 'a MReg * 'a MReg
       | MRep of 'a MReg
  val split : 'a list -> ('a list * 'a list) list
  val parts : ''a list -> ''a list list list
  val accept : ''a Reg -> ''a list -> bool
  val mark : 'a Reg -> 'a MReg
  val empty : 'a MReg -> bool
  val final : 'a MReg -> bool
  val shift : bool -> ''a MReg -> ''a -> ''a MReg
  val accept_m : ''a MReg -> ''a list -> bool
end
