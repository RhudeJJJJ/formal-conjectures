/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5105 : Family 7 := level7.get ⟨74,by decide⟩
def sourceMap5105 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,11,8,9,10,0,12,13,14,15] (sourceLabel 7 2 4 v)
def fusedMap5105 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5105_checked : acceptsGraphIso
    (source (graph core5105) (root 7) 2 4) DegreeTwoThreeSpectrum4738.graph sourceMap5105=true := by decide +kernel
theorem fusedMap5105_checked : acceptsGraphIso
    (fused (graph core5105) (root 7) 2 4) DegreeTwoThreeSpectrum3923.graph fusedMap5105=true := by decide +kernel
theorem certified5105 : Certified (graph core5105) (root 7) 2 4 :=
  of_native_maps core5105 DegreeTwoThreeSpectrum4738.graph DegreeTwoThreeSpectrum3923.graph
    sourceMap5105 fusedMap5105 sourceMap5105_checked fusedMap5105_checked
    DegreeTwoThreeFiniteComparisons.comparison5105
#print axioms sourceMap5105_checked
#print axioms fusedMap5105_checked
#print axioms certified5105
def sourceMap5105swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,11,0,12,13,14,15,8,9,10] (sourceLabel 7 4 2 v)
def fusedMap5105swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5105swap_checked : acceptsGraphIso
    (source (graph core5105) (root 7) 4 2) DegreeTwoThreeSpectrum4738.graph sourceMap5105swap=true := by decide +kernel
theorem fusedMap5105swap_checked : acceptsGraphIso
    (fused (graph core5105) (root 7) 4 2) DegreeTwoThreeSpectrum3923.graph fusedMap5105swap=true := by decide +kernel
theorem certified5105swap : Certified (graph core5105) (root 7) 4 2 :=
  of_native_maps core5105 DegreeTwoThreeSpectrum4738.graph DegreeTwoThreeSpectrum3923.graph
    sourceMap5105swap fusedMap5105swap sourceMap5105swap_checked fusedMap5105swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5105
#print axioms sourceMap5105swap_checked
#print axioms fusedMap5105swap_checked
#print axioms certified5105swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
