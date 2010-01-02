structure PrettyPrint =
struct
	fun ppdec (ExpDec {exp=exp,...}) = ppexp exp
	  | ppdec NullDec = "<NULLDEC>"
	  | ppdec (LocalDec {dec1=dec1,dec2=dec2,...}) =
	  	"local\n" ^ ppdecs dec1 ^ "\nin\n" ^ ppdecs dec2 ^ "\nend\n"
	  | ppdec (ValDec {tyvars=tyvars,valBind=valBind,recBind=recBind}) =
	  		ppbinds valBind ^ ppbinds recBind

end

