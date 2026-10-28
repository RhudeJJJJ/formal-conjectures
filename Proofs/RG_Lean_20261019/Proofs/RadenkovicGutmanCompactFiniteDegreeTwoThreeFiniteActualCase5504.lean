/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons110
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5504 : Family 6 := level6.get ⟨44,by decide⟩
def sourceMap5504 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (sourceLabel 6 2 2 v)
def fusedMap5504 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap5504_checked : acceptsGraphIso
    (source (graph core5504) (root 6) 2 2) DegreeOneSmallSpectrum1983.graph sourceMap5504=true := by decide +kernel
theorem fusedMap5504_checked : acceptsGraphIso
    (fused (graph core5504) (root 6) 2 2) DegreeOneSmallSpectrum1296.graph fusedMap5504=true := by decide +kernel
theorem certified5504 : Certified (graph core5504) (root 6) 2 2 :=
  of_native_maps core5504 DegreeOneSmallSpectrum1983.graph DegreeOneSmallSpectrum1296.graph
    sourceMap5504 fusedMap5504 sourceMap5504_checked fusedMap5504_checked
    DegreeTwoThreeFiniteComparisons.comparison5504
#print axioms sourceMap5504_checked
#print axioms fusedMap5504_checked
#print axioms certified5504
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
