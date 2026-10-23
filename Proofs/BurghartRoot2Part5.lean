import Proofs.BurghartFringeData
/-! # Root 2 leaf-subset class 5 -/
set_option Elab.async false
set_option maxRecDepth 100000
namespace BurghartLists
open BurghartCertificate
set_option maxHeartbeats 0 in
theorem root2_part5 : norm1 (fringePart T2 distances2 0 5) = rootParts2 5 := by decide +kernel
#print axioms root2_part5
end BurghartLists
