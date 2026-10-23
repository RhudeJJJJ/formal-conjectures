import Proofs.BurghartFringeData
/-! # Root 1 leaf-subset class 8 -/
set_option Elab.async false
set_option maxRecDepth 100000
namespace BurghartLists
open BurghartCertificate
set_option maxHeartbeats 0 in
theorem root1_part8 : norm1 (fringePart T1 distances1 0 8) = rootParts1 8 := by decide +kernel
#print axioms root1_part8
end BurghartLists
