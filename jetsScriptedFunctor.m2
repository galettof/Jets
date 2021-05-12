restart
needsPackage "Jets"

JJ = new ScriptedFunctor from {
     subscript => (
	  i -> new ScriptedFunctor from {
	       argument => (X -> (
	       	    	 {Projective => false} >> opts -> Y -> (
		    	      f := lookup(jets,class i,class Y);
		    	      if f === null then error "no method available"
		    	      else (f opts)(i,Y)
			      )
	       	    	 ) X
	       	    )
	       }
	  )
     }

R=QQ[x,y,z]
S=QQ[t]
f=map(S,R,{t,t^2,t^3})
f2=JJ_2 f
K=ker f2
I=JJ_2 ideal(y-x^2,z-x^3)
I==K

--suggestions: change opts in Jets.m2 to JetsOptions (as done for Tor)
--then replace {Projective=>false} above with JetsOptions
--this way JetsOptions need only be defined once at the beginning
