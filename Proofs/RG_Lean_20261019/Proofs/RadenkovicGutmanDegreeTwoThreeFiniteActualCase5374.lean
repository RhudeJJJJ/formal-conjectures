/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5374 : Family 4 := level4.get ⟨5,by decide⟩
def sourceMap5374 : (Vertices 4 ⊕ Fin 5 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,11,12,13,14,1,2,3,4,5,6,7,8,9,10] (sourceLabel 4 4 4 v)
def fusedMap5374 : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14] (fusedLabel 4 4 4 v)
theorem sourceMap5374_checked : acceptsGraphIso
    (source (graph core5374) (root 4) 4 4) DegreeTwoThreeSpectrum2995.graph sourceMap5374=true := by decide +kernel
theorem fusedMap5374_checked : acceptsGraphIso
    (fused (graph core5374) (root 4) 4 4) DegreeTwoThreeSpectrum2327.graph fusedMap5374=true := by decide +kernel
theorem certified5374 : Certified (graph core5374) (root 4) 4 4 :=
  of_native_maps core5374 DegreeTwoThreeSpectrum2995.graph DegreeTwoThreeSpectrum2327.graph
    sourceMap5374 fusedMap5374 sourceMap5374_checked fusedMap5374_checked
    DegreeTwoThreeFiniteComparisons.comparison5374
#print axioms sourceMap5374_checked
#print axioms fusedMap5374_checked
#print axioms certified5374
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
