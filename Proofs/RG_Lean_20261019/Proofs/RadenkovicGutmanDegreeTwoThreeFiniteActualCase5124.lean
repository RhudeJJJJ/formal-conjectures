/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5124 : Family 8 := level8.get ⟨31,by decide⟩
def sourceMap5124 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,10,11,12,13,14,15,16,9,6,7,8,1,2,3,4,5] (sourceLabel 8 2 4 v)
def fusedMap5124 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5124_checked : acceptsGraphIso
    (source (graph core5124) (root 8) 2 4) DegreeTwoThreeSpectrum5924.graph sourceMap5124=true := by decide +kernel
theorem fusedMap5124_checked : acceptsGraphIso
    (fused (graph core5124) (root 8) 2 4) DegreeTwoThreeSpectrum5119.graph fusedMap5124=true := by decide +kernel
theorem certified5124 : Certified (graph core5124) (root 8) 2 4 :=
  of_native_maps core5124 DegreeTwoThreeSpectrum5924.graph DegreeTwoThreeSpectrum5119.graph
    sourceMap5124 fusedMap5124 sourceMap5124_checked fusedMap5124_checked
    DegreeTwoThreeFiniteComparisons.comparison5124
#print axioms sourceMap5124_checked
#print axioms fusedMap5124_checked
#print axioms certified5124
def sourceMap5124swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,10,11,12,13,14,15,16,9,1,2,3,4,5,6,7,8] (sourceLabel 8 4 2 v)
def fusedMap5124swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5124swap_checked : acceptsGraphIso
    (source (graph core5124) (root 8) 4 2) DegreeTwoThreeSpectrum5924.graph sourceMap5124swap=true := by decide +kernel
theorem fusedMap5124swap_checked : acceptsGraphIso
    (fused (graph core5124) (root 8) 4 2) DegreeTwoThreeSpectrum5119.graph fusedMap5124swap=true := by decide +kernel
theorem certified5124swap : Certified (graph core5124) (root 8) 4 2 :=
  of_native_maps core5124 DegreeTwoThreeSpectrum5924.graph DegreeTwoThreeSpectrum5119.graph
    sourceMap5124swap fusedMap5124swap sourceMap5124swap_checked fusedMap5124swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5124
#print axioms sourceMap5124swap_checked
#print axioms fusedMap5124swap_checked
#print axioms certified5124swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
