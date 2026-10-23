import Proofs.BurghartFringeData
/-! # Root 2 leaf-subset class 2 -/
set_option Elab.async false
set_option maxRecDepth 100000
namespace BurghartLists
open BurghartCertificate
set_option maxHeartbeats 0 in
theorem root2_part2 : norm1 (fringePart T2 distances2 0 2) = rootParts2 2 := by decide +kernel
#print axioms root2_part2
end BurghartLists
