import Dihedral.alternatingword
example (i j : Fin 2) (k : Nat) : (alternatingWord i j (2*k+1)).head? = some j := by
  simpa using alternatingWord_head_odd i j k
