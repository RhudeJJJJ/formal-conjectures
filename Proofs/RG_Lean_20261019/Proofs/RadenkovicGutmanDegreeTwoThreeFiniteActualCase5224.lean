/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5224 : Family 5 := level5.get ⟨14,by decide⟩
def sourceMap5224 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,5,6,7,8,9,2,3,4,0,10,11,12,13,14] (sourceLabel 5 2 5 v)
def fusedMap5224 : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 2 5 v)
theorem sourceMap5224_checked : acceptsGraphIso
    (source (graph core5224) (root 5) 2 5) DegreeTwoThreeSpectrum2827.graph sourceMap5224=true := by decide +kernel
theorem fusedMap5224_checked : acceptsGraphIso
    (fused (graph core5224) (root 5) 2 5) DegreeTwoThreeSpectrum2315.graph fusedMap5224=true := by decide +kernel
theorem certified5224 : Certified (graph core5224) (root 5) 2 5 :=
  of_native_maps core5224 DegreeTwoThreeSpectrum2827.graph DegreeTwoThreeSpectrum2315.graph
    sourceMap5224 fusedMap5224 sourceMap5224_checked fusedMap5224_checked
    DegreeTwoThreeFiniteComparisons.comparison5224
#print axioms sourceMap5224_checked
#print axioms fusedMap5224_checked
#print axioms certified5224
def sourceMap5224swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,5,6,7,8,9,0,10,11,12,13,14,2,3,4] (sourceLabel 5 5 2 v)
def fusedMap5224swap : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 5 2 v)
theorem sourceMap5224swap_checked : acceptsGraphIso
    (source (graph core5224) (root 5) 5 2) DegreeTwoThreeSpectrum2827.graph sourceMap5224swap=true := by decide +kernel
theorem fusedMap5224swap_checked : acceptsGraphIso
    (fused (graph core5224) (root 5) 5 2) DegreeTwoThreeSpectrum2315.graph fusedMap5224swap=true := by decide +kernel
theorem certified5224swap : Certified (graph core5224) (root 5) 5 2 :=
  of_native_maps core5224 DegreeTwoThreeSpectrum2827.graph DegreeTwoThreeSpectrum2315.graph
    sourceMap5224swap fusedMap5224swap sourceMap5224swap_checked fusedMap5224swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5224
#print axioms sourceMap5224swap_checked
#print axioms fusedMap5224swap_checked
#print axioms certified5224swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
