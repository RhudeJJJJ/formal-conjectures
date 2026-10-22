/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5429 : Family 5 := level5.get ⟨16,by decide⟩
def sourceMap5429 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 1) → Fin 8 :=
  fun v => ![0,5,6,7,1,2,3,4] (sourceLabel 5 0 0 v)
def fusedMap5429 : (Vertices 5 ⊕ Fin 2) → Fin 8 :=
  fun v => ![0,1,2,3,6,7,4,5] (fusedLabel 5 0 0 v)
theorem sourceMap5429_checked : acceptsGraphIso
    (source (graph core5429) (root 5) 0 0) DegreeOneSmallSpectrum027.graph sourceMap5429=true := by decide +kernel
theorem fusedMap5429_checked : acceptsGraphIso
    (fused (graph core5429) (root 5) 0 0) DegreeOneSmallSpectrum033.graph fusedMap5429=true := by decide +kernel
theorem certified5429 : Certified (graph core5429) (root 5) 0 0 :=
  of_native_maps core5429 DegreeOneSmallSpectrum027.graph DegreeOneSmallSpectrum033.graph
    sourceMap5429 fusedMap5429 sourceMap5429_checked fusedMap5429_checked
    DegreeTwoThreeFiniteComparisons.comparison5429
#print axioms sourceMap5429_checked
#print axioms fusedMap5429_checked
#print axioms certified5429
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
