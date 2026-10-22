/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5255 : Family 7 := level7.get ⟨48,by decide⟩
def sourceMap5255 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,10,11,7,8,9,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5255 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5255_checked : acceptsGraphIso
    (source (graph core5255) (root 7) 2 5) DegreeTwoThreeSpectrum6764.graph sourceMap5255=true := by decide +kernel
theorem fusedMap5255_checked : acceptsGraphIso
    (fused (graph core5255) (root 7) 2 5) DegreeTwoThreeSpectrum5028.graph fusedMap5255=true := by decide +kernel
theorem certified5255 : Certified (graph core5255) (root 7) 2 5 :=
  of_native_maps core5255 DegreeTwoThreeSpectrum6764.graph DegreeTwoThreeSpectrum5028.graph
    sourceMap5255 fusedMap5255 sourceMap5255_checked fusedMap5255_checked
    DegreeTwoThreeFiniteComparisons.comparison5255
#print axioms sourceMap5255_checked
#print axioms fusedMap5255_checked
#print axioms certified5255
def sourceMap5255swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,10,11,0,12,13,14,15,16,7,8,9] (sourceLabel 7 5 2 v)
def fusedMap5255swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5255swap_checked : acceptsGraphIso
    (source (graph core5255) (root 7) 5 2) DegreeTwoThreeSpectrum6764.graph sourceMap5255swap=true := by decide +kernel
theorem fusedMap5255swap_checked : acceptsGraphIso
    (fused (graph core5255) (root 7) 5 2) DegreeTwoThreeSpectrum5028.graph fusedMap5255swap=true := by decide +kernel
theorem certified5255swap : Certified (graph core5255) (root 7) 5 2 :=
  of_native_maps core5255 DegreeTwoThreeSpectrum6764.graph DegreeTwoThreeSpectrum5028.graph
    sourceMap5255swap fusedMap5255swap sourceMap5255swap_checked fusedMap5255swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5255
#print axioms sourceMap5255swap_checked
#print axioms fusedMap5255swap_checked
#print axioms certified5255swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
