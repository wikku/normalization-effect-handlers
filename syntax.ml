type typ = Var of string | Arrow of typ * tar | Forall of string * typ
and eff = Op of typ * typ | Forall of eff
and row = eff list
and tar = typ * row
