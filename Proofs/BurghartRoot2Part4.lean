import Proofs.BurghartFringeData
/-! # Root 2 leaf-subset class 4 -/
set_option Elab.async false
set_option maxRecDepth 100000
namespace BurghartLists
open BurghartCertificate
set_option maxHeartbeats 0 in
theorem root2_part4 : norm1 (fringePart T2 distances2 0 4) = rootParts2 4 := by
  rw [fringePart_root_eq_fast T2 distances2 rootLeaves2 ancestors2
    rootLeaves2_eq rootPaths2_eq (4:Fin 16)]
  decide +kernel
#print axioms root2_part4
end BurghartLists
