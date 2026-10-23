import Proofs.BurghartFringeData
/-! # Root 2 leaf-subset class 15 -/
set_option Elab.async false
set_option maxRecDepth 100000
namespace BurghartLists
open BurghartCertificate
set_option maxHeartbeats 0 in
theorem root2_part15 : norm1 (fringePart T2 distances2 0 15) = rootParts2 15 := by decide +kernel
#print axioms root2_part15
end BurghartLists
