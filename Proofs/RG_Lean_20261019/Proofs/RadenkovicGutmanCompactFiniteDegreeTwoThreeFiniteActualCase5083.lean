/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5083 : Family 7 := level7.get ⟨11,by decide⟩
def sourceMap5083 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,15,12,13,14,7,8,9,10,11] (sourceLabel 7 2 4 v)
def fusedMap5083 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5083_checked : acceptsGraphIso
    (source (graph core5083) (root 7) 2 4) DegreeTwoThreeSpectrum4388.graph sourceMap5083=true := by decide +kernel
theorem fusedMap5083_checked : acceptsGraphIso
    (fused (graph core5083) (root 7) 2 4) DegreeTwoThreeSpectrum3858.graph fusedMap5083=true := by decide +kernel
theorem certified5083 : Certified (graph core5083) (root 7) 2 4 :=
  of_native_maps core5083 DegreeTwoThreeSpectrum4388.graph DegreeTwoThreeSpectrum3858.graph
    sourceMap5083 fusedMap5083 sourceMap5083_checked fusedMap5083_checked
    DegreeTwoThreeFiniteComparisons.comparison5083
#print axioms sourceMap5083_checked
#print axioms fusedMap5083_checked
#print axioms certified5083
def sourceMap5083swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,15,7,8,9,10,11,12,13,14] (sourceLabel 7 4 2 v)
def fusedMap5083swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5083swap_checked : acceptsGraphIso
    (source (graph core5083) (root 7) 4 2) DegreeTwoThreeSpectrum4388.graph sourceMap5083swap=true := by decide +kernel
theorem fusedMap5083swap_checked : acceptsGraphIso
    (fused (graph core5083) (root 7) 4 2) DegreeTwoThreeSpectrum3858.graph fusedMap5083swap=true := by decide +kernel
theorem certified5083swap : Certified (graph core5083) (root 7) 4 2 :=
  of_native_maps core5083 DegreeTwoThreeSpectrum4388.graph DegreeTwoThreeSpectrum3858.graph
    sourceMap5083swap fusedMap5083swap sourceMap5083swap_checked fusedMap5083swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5083
#print axioms sourceMap5083swap_checked
#print axioms fusedMap5083swap_checked
#print axioms certified5083swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
