/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5128 : Family 8 := level8.get ⟨47,by decide⟩
def sourceMap5128 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,16,13,14,15,8,9,10,11,12] (sourceLabel 8 2 4 v)
def fusedMap5128 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5128_checked : acceptsGraphIso
    (source (graph core5128) (root 8) 2 4) DegreeTwoThreeSpectrum6416.graph sourceMap5128=true := by decide +kernel
theorem fusedMap5128_checked : acceptsGraphIso
    (fused (graph core5128) (root 8) 2 4) DegreeTwoThreeSpectrum4984.graph fusedMap5128=true := by decide +kernel
theorem certified5128 : Certified (graph core5128) (root 8) 2 4 :=
  of_native_maps core5128 DegreeTwoThreeSpectrum6416.graph DegreeTwoThreeSpectrum4984.graph
    sourceMap5128 fusedMap5128 sourceMap5128_checked fusedMap5128_checked
    DegreeTwoThreeFiniteComparisons.comparison5128
#print axioms sourceMap5128_checked
#print axioms fusedMap5128_checked
#print axioms certified5128
def sourceMap5128swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,16,8,9,10,11,12,13,14,15] (sourceLabel 8 4 2 v)
def fusedMap5128swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5128swap_checked : acceptsGraphIso
    (source (graph core5128) (root 8) 4 2) DegreeTwoThreeSpectrum6416.graph sourceMap5128swap=true := by decide +kernel
theorem fusedMap5128swap_checked : acceptsGraphIso
    (fused (graph core5128) (root 8) 4 2) DegreeTwoThreeSpectrum4984.graph fusedMap5128swap=true := by decide +kernel
theorem certified5128swap : Certified (graph core5128) (root 8) 4 2 :=
  of_native_maps core5128 DegreeTwoThreeSpectrum6416.graph DegreeTwoThreeSpectrum4984.graph
    sourceMap5128swap fusedMap5128swap sourceMap5128swap_checked fusedMap5128swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5128
#print axioms sourceMap5128swap_checked
#print axioms fusedMap5128swap_checked
#print axioms certified5128swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
