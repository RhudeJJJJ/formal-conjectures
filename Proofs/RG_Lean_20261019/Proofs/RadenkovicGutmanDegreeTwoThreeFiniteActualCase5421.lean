/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5421 : Family 4 := level4.get ⟨6,by decide⟩
def sourceMap5421 : (Vertices 4 ⊕ Fin 6 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,13,14,15,16,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 4 5 5 v)
def fusedMap5421 : (Vertices 4 ⊕ Fin 12) → Fin 17 :=
  fun v => ![5,6,7,8,9,4,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 4 5 5 v)
theorem sourceMap5421_checked : acceptsGraphIso
    (source (graph core5421) (root 4) 5 5) DegreeTwoThreeSpectrum5959.graph sourceMap5421=true := by decide +kernel
theorem fusedMap5421_checked : acceptsGraphIso
    (fused (graph core5421) (root 4) 5 5) DegreeTwoThreeSpectrum5014.graph fusedMap5421=true := by decide +kernel
theorem certified5421 : Certified (graph core5421) (root 4) 5 5 :=
  of_native_maps core5421 DegreeTwoThreeSpectrum5959.graph DegreeTwoThreeSpectrum5014.graph
    sourceMap5421 fusedMap5421 sourceMap5421_checked fusedMap5421_checked
    DegreeTwoThreeFiniteComparisons.comparison5421
#print axioms sourceMap5421_checked
#print axioms fusedMap5421_checked
#print axioms certified5421
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
