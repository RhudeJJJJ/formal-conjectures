/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5497 : Family 5 := level5.get ⟨17,by decide⟩
def sourceMap5497 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,1,2,3,4,5,6] (sourceLabel 5 2 2 v)
def fusedMap5497 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (fusedLabel 5 2 2 v)
theorem sourceMap5497_checked : acceptsGraphIso
    (source (graph core5497) (root 5) 2 2) SmallGeFourSpectrum194.graph sourceMap5497=true := by decide +kernel
theorem fusedMap5497_checked : acceptsGraphIso
    (fused (graph core5497) (root 5) 2 2) DegreeOneSmallSpectrum505.graph fusedMap5497=true := by decide +kernel
theorem certified5497 : Certified (graph core5497) (root 5) 2 2 :=
  of_native_maps core5497 SmallGeFourSpectrum194.graph DegreeOneSmallSpectrum505.graph
    sourceMap5497 fusedMap5497 sourceMap5497_checked fusedMap5497_checked
    DegreeTwoThreeFiniteComparisons.comparison5497
#print axioms sourceMap5497_checked
#print axioms fusedMap5497_checked
#print axioms certified5497
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
