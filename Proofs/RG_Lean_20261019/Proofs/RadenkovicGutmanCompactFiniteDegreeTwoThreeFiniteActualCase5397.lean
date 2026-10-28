/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5397 : Family 6 := level6.get ⟨41,by decide⟩
def sourceMap5397 : (Vertices 6 ⊕ Fin 5 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 4 4 v)
def fusedMap5397 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,10,3,2,1,0,11,12,13,14,15,16] (fusedLabel 6 4 4 v)
theorem sourceMap5397_checked : acceptsGraphIso
    (source (graph core5397) (root 6) 4 4) DegreeTwoThreeSpectrum7056.graph sourceMap5397=true := by decide +kernel
theorem fusedMap5397_checked : acceptsGraphIso
    (fused (graph core5397) (root 6) 4 4) DegreeTwoThreeSpectrum5228.graph fusedMap5397=true := by decide +kernel
theorem certified5397 : Certified (graph core5397) (root 6) 4 4 :=
  of_native_maps core5397 DegreeTwoThreeSpectrum7056.graph DegreeTwoThreeSpectrum5228.graph
    sourceMap5397 fusedMap5397 sourceMap5397_checked fusedMap5397_checked
    DegreeTwoThreeFiniteComparisons.comparison5397
#print axioms sourceMap5397_checked
#print axioms fusedMap5397_checked
#print axioms certified5397
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
