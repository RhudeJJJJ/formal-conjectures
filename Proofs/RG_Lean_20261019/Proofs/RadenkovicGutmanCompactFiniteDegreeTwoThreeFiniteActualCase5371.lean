/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5371 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap5371 : (Vertices 2 ⊕ Fin 5 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,11,12,1,2,3,4,5,6,7,8,9,10] (sourceLabel 2 4 4 v)
def fusedMap5371 : (Vertices 2 ⊕ Fin 10) → Fin 13 :=
  fun v => ![4,5,6,3,2,1,0,7,8,9,10,11,12] (fusedLabel 2 4 4 v)
theorem sourceMap5371_checked : acceptsGraphIso
    (source (graph core5371) (root 2) 4 4) DegreeOneSmallSpectrum978.graph sourceMap5371=true := by decide +kernel
theorem fusedMap5371_checked : acceptsGraphIso
    (fused (graph core5371) (root 2) 4 4) DegreeOneSmallSpectrum856.graph fusedMap5371=true := by decide +kernel
theorem certified5371 : Certified (graph core5371) (root 2) 4 4 :=
  of_native_maps core5371 DegreeOneSmallSpectrum978.graph DegreeOneSmallSpectrum856.graph
    sourceMap5371 fusedMap5371 sourceMap5371_checked fusedMap5371_checked
    DegreeTwoThreeFiniteComparisons.comparison5371
#print axioms sourceMap5371_checked
#print axioms fusedMap5371_checked
#print axioms certified5371
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
