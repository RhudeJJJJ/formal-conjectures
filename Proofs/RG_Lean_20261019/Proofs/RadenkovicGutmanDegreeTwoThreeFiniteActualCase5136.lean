/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5136 : Family 8 := level8.get ⟨74,by decide⟩
def sourceMap5136 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,16,13,14,15,8,9,10,11,12] (sourceLabel 8 2 4 v)
def fusedMap5136 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5136_checked : acceptsGraphIso
    (source (graph core5136) (root 8) 2 4) DegreeTwoThreeSpectrum6929.graph sourceMap5136=true := by decide +kernel
theorem fusedMap5136_checked : acceptsGraphIso
    (fused (graph core5136) (root 8) 2 4) DegreeTwoThreeSpectrum5052.graph fusedMap5136=true := by decide +kernel
theorem certified5136 : Certified (graph core5136) (root 8) 2 4 :=
  of_native_maps core5136 DegreeTwoThreeSpectrum6929.graph DegreeTwoThreeSpectrum5052.graph
    sourceMap5136 fusedMap5136 sourceMap5136_checked fusedMap5136_checked
    DegreeTwoThreeFiniteComparisons.comparison5136
#print axioms sourceMap5136_checked
#print axioms fusedMap5136_checked
#print axioms certified5136
def sourceMap5136swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,16,8,9,10,11,12,13,14,15] (sourceLabel 8 4 2 v)
def fusedMap5136swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5136swap_checked : acceptsGraphIso
    (source (graph core5136) (root 8) 4 2) DegreeTwoThreeSpectrum6929.graph sourceMap5136swap=true := by decide +kernel
theorem fusedMap5136swap_checked : acceptsGraphIso
    (fused (graph core5136) (root 8) 4 2) DegreeTwoThreeSpectrum5052.graph fusedMap5136swap=true := by decide +kernel
theorem certified5136swap : Certified (graph core5136) (root 8) 4 2 :=
  of_native_maps core5136 DegreeTwoThreeSpectrum6929.graph DegreeTwoThreeSpectrum5052.graph
    sourceMap5136swap fusedMap5136swap sourceMap5136swap_checked fusedMap5136swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5136
#print axioms sourceMap5136swap_checked
#print axioms fusedMap5136swap_checked
#print axioms certified5136swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
