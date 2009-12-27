structure Lml =
struct
  fun lml (lmlfile, specfile) = 
    let 
       val (sc,fc) = Spec.check (Behav.btype lmlfile) (ParseSpec.parse specfile)
    in
       if sc andalso fc then (print "Specification satisfied.\n") else ()
    end handle (Fail e) => print ("ERROR: " ^ e ^ "\n")
end

structure Main =
struct
	fun main () = 
		let val args = CommandLine.arguments ()
		in (Lml.lml (hd args, hd (tl args));()) end
end

val _ = Main.main ()

