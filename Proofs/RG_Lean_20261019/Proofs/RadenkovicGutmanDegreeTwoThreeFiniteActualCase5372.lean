/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5372 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap5372 : (Vertices 3 ⊕ Fin 5 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,11,12,13,1,2,3,4,5,6,7,8,9,10] (sourceLabel 3 4 4 v)
def fusedMap5372 : (Vertices 3 ⊕ Fin 10) → Fin 14 :=
  fun v => ![4,5,6,7,3,2,1,0,8,9,10,11,12,13] (fusedLabel 3 4 4 v)
theorem sourceMap5372_checked : acceptsGraphIso
    (source (graph core5372) (root 3) 4 4) DegreeTwoThreeSpectrum1924.graph sourceMap5372=true := by decide +kernel
theorem fusedMap5372_checked : acceptsGraphIso
    (fused (graph core5372) (root 3) 4 4) DegreeTwoThreeSpectrum1722.graph fusedMap5372=true := by decide +kernel
theorem certified5372 : Certified (graph core5372) (root 3) 4 4 :=
  of_native_maps core5372 DegreeTwoThreeSpectrum1924.graph DegreeTwoThreeSpectrum1722.graph
    sourceMap5372 fusedMap5372 sourceMap5372_checked fusedMap5372_checked
    DegreeTwoThreeFiniteComparisons.comparison5372
#print axioms sourceMap5372_checked
#print axioms fusedMap5372_checked
#print axioms certified5372
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
