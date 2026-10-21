/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons110
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5500 : Family 6 := level6.get ⟨32,by decide⟩
def sourceMap5500 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,11,12,5,6,7,8,9,10] (sourceLabel 6 2 2 v)
def fusedMap5500 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap5500_checked : acceptsGraphIso
    (source (graph core5500) (root 6) 2 2) DegreeOneSmallSpectrum1964.graph sourceMap5500=true := by decide +kernel
theorem fusedMap5500_checked : acceptsGraphIso
    (fused (graph core5500) (root 6) 2 2) DegreeOneSmallSpectrum924.graph fusedMap5500=true := by decide +kernel
theorem certified5500 : Certified (graph core5500) (root 6) 2 2 :=
  of_native_maps core5500 DegreeOneSmallSpectrum1964.graph DegreeOneSmallSpectrum924.graph
    sourceMap5500 fusedMap5500 sourceMap5500_checked fusedMap5500_checked
    DegreeTwoThreeFiniteComparisons.comparison5500
#print axioms sourceMap5500_checked
#print axioms fusedMap5500_checked
#print axioms certified5500
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
