structure regexpML :> regexpML =
struct
  nonfix accept_m shift final empty mark accept parts split MRep MSeq
         MAlt MSym MEps Rep Seq Alt Sym Eps * / div mod + - ^ @ <> > <
         >= <= := o before;

  open listML

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
  fun split [] = [([],[])]
    | split (c::cs) =
        ([],c::cs)::
        MAP (fn x => (c::pairML.FST x,pairML.SND x)) (split cs)

  fun parts [] = [[]]
    | parts (c::cs) =
        (if cs = [] then
           [[[c]]]
         else FLAT (MAP (fn x => [[c]::x,(c::HD x)::TL x]) (parts cs)))

  fun accept Eps u = (u = [])
    | accept (Sym(c)) u = (u = [c])
    | accept (Alt(p,q)) u = accept p u orelse accept q u
    | accept (Seq(p,q)) u =
        EXISTS (fn x =>
          accept p (pairML.FST x) andalso accept q (pairML.SND x))
          (split u)
    | accept (Rep(r)) u =
        EXISTS (fn partition =>
          EVERY (fn part => accept r part) partition) (parts u)

  fun mark Eps = MEps
    | mark (Sym(x)) = MSym(false,x)
    | mark (Alt(p,q)) = MAlt(mark p,mark q)
    | mark (Seq(p,q)) = MSeq(mark p,mark q)
    | mark (Rep(r)) = MRep(mark r)

  fun empty MEps = true
    | empty (MSym(v0,v1)) = false
    | empty (MAlt(p,q)) = empty p orelse empty q
    | empty (MSeq(p,q)) = empty p andalso empty q
    | empty (MRep(v2)) = true

  fun final MEps = false
    | final (MSym(b,v0)) = b
    | final (MAlt(p,q)) = final p orelse final q
    | final (MSeq(p,q)) = final p andalso empty q orelse final q
    | final (MRep(r)) = final r

  fun shift v0 MEps v1 = MEps
    | shift m (MSym(v2,x)) c = MSym(m andalso (x = c),x)
    | shift m (MAlt(p,q)) c = MAlt(shift m p c,shift m q c)
    | shift m (MSeq(p,q)) c =
        MSeq(shift m p c,shift (m andalso empty p orelse final p) q c)
    | shift m (MRep(r)) c = MRep(shift (m orelse final r) r c)

  fun accept_m r [] = empty r
    | accept_m r (c::cs) =
        final (FOLDL (shift false) (shift true r c) cs)

end
