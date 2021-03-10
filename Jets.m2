newPackage(
     "Jets",
     Version => "0.1",
     Date => "March 9, 2021",
     AuxiliaryFiles => false,
     Authors => {
	 {
	     Name => "Federico Galetto",
	     Email => "galetto.federico@gmail.com",
	     HomePage => "http://math.galetto.org"
	     }
	   },
     Headline => "compute jet functors",
     PackageImports => {"SimpleDoc"},
     DebuggingMode => false
     )

-- all user facing symbols, methods, and types must be exported
export {
    "jets"
    }

