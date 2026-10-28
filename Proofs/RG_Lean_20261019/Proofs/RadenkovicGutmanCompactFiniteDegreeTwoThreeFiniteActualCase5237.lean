/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5237 : Family 6 := level6.get ⟨33,by decide⟩
def sourceMap5237 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 6 2 5 v)
def fusedMap5237 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 2 5 v)
theorem sourceMap5237_checked : acceptsGraphIso
    (source (graph core5237) (root 6) 2 5) DegreeTwoThreeSpectrum4539.graph sourceMap5237=true := by decide +kernel
theorem fusedMap5237_checked : acceptsGraphIso
    (fused (graph core5237) (root 6) 2 5) DegreeTwoThreeSpectrum4062.graph fusedMap5237=true := by decide +kernel
theorem certified5237 : Certified (graph core5237) (root 6) 2 5 :=
  of_native_maps core5237 DegreeTwoThreeSpectrum4539.graph DegreeTwoThreeSpectrum4062.graph
    sourceMap5237 fusedMap5237 sourceMap5237_checked fusedMap5237_checked
    DegreeTwoThreeFiniteComparisons.comparison5237
#print axioms sourceMap5237_checked
#print axioms fusedMap5237_checked
#print axioms certified5237
def sourceMap5237swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,0,11,12,13,14,15,8,9,10] (sourceLabel 6 5 2 v)
def fusedMap5237swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 5 2 v)
theorem sourceMap5237swap_checked : acceptsGraphIso
    (source (graph core5237) (root 6) 5 2) DegreeTwoThreeSpectrum4539.graph sourceMap5237swap=true := by decide +kernel
theorem fusedMap5237swap_checked : acceptsGraphIso
    (fused (graph core5237) (root 6) 5 2) DegreeTwoThreeSpectrum4062.graph fusedMap5237swap=true := by decide +kernel
theorem certified5237swap : Certified (graph core5237) (root 6) 5 2 :=
  of_native_maps core5237 DegreeTwoThreeSpectrum4539.graph DegreeTwoThreeSpectrum4062.graph
    sourceMap5237swap fusedMap5237swap sourceMap5237swap_checked fusedMap5237swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5237
#print axioms sourceMap5237swap_checked
#print axioms fusedMap5237swap_checked
#print axioms certified5237swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
