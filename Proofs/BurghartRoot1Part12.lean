import Proofs.BurghartFringeData
/-! # Root 1 leaf-subset class 12 -/
set_option Elab.async false
set_option maxRecDepth 100000
namespace BurghartLists
open BurghartCertificate
set_option maxHeartbeats 0 in
theorem root1_part12 : norm1 (fringePart T1 distances1 0 12) = rootParts1 12 := by decide +kernel
#print axioms root1_part12
end BurghartLists
