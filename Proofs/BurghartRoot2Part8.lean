import Proofs.BurghartFringeData
/-! # Root 2 leaf-subset class 8 -/
set_option Elab.async false
set_option maxRecDepth 100000
namespace BurghartLists
open BurghartCertificate
set_option maxHeartbeats 0 in
theorem root2_part8 : norm1 (fringePart T2 distances2 0 8) = rootParts2 8 := by decide +kernel
#print axioms root2_part8
end BurghartLists
