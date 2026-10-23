import Proofs.BurghartFringeData
/-! # Root 1 leaf-subset class 4 -/
set_option Elab.async false
set_option maxRecDepth 100000
namespace BurghartLists
open BurghartCertificate
set_option maxHeartbeats 0 in
theorem root1_part4 : norm1 (fringePart T1 distances1 0 4) = rootParts1 4 := by
  rw [fringePart_root_eq_fast T1 distances1 rootLeaves1 ancestors1
    rootLeaves1_eq rootPaths1_eq (4:Fin 16)]
  decide +kernel
#print axioms root1_part4
end BurghartLists
