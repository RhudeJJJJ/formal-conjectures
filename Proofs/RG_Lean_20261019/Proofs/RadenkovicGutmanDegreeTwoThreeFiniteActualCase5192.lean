/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5192 : Family 8 := level8.get ⟨215,by decide⟩
def sourceMap5192 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,12,9,10,11,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5192 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5192_checked : acceptsGraphIso
    (source (graph core5192) (root 8) 2 4) DegreeTwoThreeSpectrum7210.graph sourceMap5192=true := by decide +kernel
theorem fusedMap5192_checked : acceptsGraphIso
    (fused (graph core5192) (root 8) 2 4) DegreeTwoThreeSpectrum5247.graph fusedMap5192=true := by decide +kernel
theorem certified5192 : Certified (graph core5192) (root 8) 2 4 :=
  of_native_maps core5192 DegreeTwoThreeSpectrum7210.graph DegreeTwoThreeSpectrum5247.graph
    sourceMap5192 fusedMap5192 sourceMap5192_checked fusedMap5192_checked
    DegreeTwoThreeFiniteComparisons.comparison5192
#print axioms sourceMap5192_checked
#print axioms fusedMap5192_checked
#print axioms certified5192
def sourceMap5192swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,12,0,13,14,15,16,9,10,11] (sourceLabel 8 4 2 v)
def fusedMap5192swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5192swap_checked : acceptsGraphIso
    (source (graph core5192) (root 8) 4 2) DegreeTwoThreeSpectrum7210.graph sourceMap5192swap=true := by decide +kernel
theorem fusedMap5192swap_checked : acceptsGraphIso
    (fused (graph core5192) (root 8) 4 2) DegreeTwoThreeSpectrum5247.graph fusedMap5192swap=true := by decide +kernel
theorem certified5192swap : Certified (graph core5192) (root 8) 4 2 :=
  of_native_maps core5192 DegreeTwoThreeSpectrum7210.graph DegreeTwoThreeSpectrum5247.graph
    sourceMap5192swap fusedMap5192swap sourceMap5192swap_checked fusedMap5192swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5192
#print axioms sourceMap5192swap_checked
#print axioms fusedMap5192swap_checked
#print axioms certified5192swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
