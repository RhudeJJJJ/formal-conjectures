import Proofs.BurghartFringeData
/-! # Root 2 leaf-subset class 1 -/
set_option Elab.async false
set_option maxRecDepth 100000
namespace BurghartLists
open BurghartCertificate
set_option maxHeartbeats 0 in
theorem root2_part1 : norm1 (fringePart T2 distances2 0 1) = rootParts2 1 := by
  rw [fringePart_root_eq_fast T2 distances2 rootLeaves2 ancestors2
    rootLeaves2_eq rootPaths2_eq (1:Fin 16)]
  decide +kernel
#print axioms root2_part1
end BurghartLists
