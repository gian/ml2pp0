structure Specification =
struct
  open Set

  type action = string

  datatype specpart =
     Action of action 
   | Repetition of specpart (* equivalent to foobar* *)
   | Alternation of specpart * specpart (* a|b *)
   | Wildcard (* Match anything *)

  type spec = {operations : action set, necessary : specpart list, safe : specpart list, forbidden : specpart list}
    
  fun spec2txt (s : spec) = ("OPERATIONS\n" ^ op2txt (#operations s) ^ "\nNECESSARY\n" ^ specpart2txt (#necessary s) ^
                           "\nSAFE\n" ^ specpart2txt (#safe s) ^ "\nFORBIDDEN\n" ^ specpart2txt (#forbidden s) ^ "\n")
  and op2txt [] = "\n"
    | op2txt (h::t) = h ^ "\n" ^ (op2txt t)
  and specpart2txt s = String.concatWith ", " (map ppspecpart s)
  and ppspecpart (Action s) = s
    | ppspecpart (Repetition x) = ppspecpart x ^ "*"
    | ppspecpart (Alternation(x,y)) = "(" ^ ppspecpart x ^ "|" ^ ppspecpart y ^ ")"
    | ppspecpart Wildcard = "_"

end
