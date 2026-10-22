/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5288 : Family 5 := level5.get ⟨14,by decide⟩
def sourceMap5288 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,6,7,8,9,10,3,4,5,1,0,11,12,13,14,15] (sourceLabel 5 2 6 v)
def fusedMap5288 : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15] (fusedLabel 5 2 6 v)
theorem sourceMap5288_checked : acceptsGraphIso
    (source (graph core5288) (root 5) 2 6) DegreeTwoThreeSpectrum4566.graph sourceMap5288=true := by decide +kernel
theorem fusedMap5288_checked : acceptsGraphIso
    (fused (graph core5288) (root 5) 2 6) DegreeTwoThreeSpectrum3902.graph fusedMap5288=true := by decide +kernel
theorem certified5288 : Certified (graph core5288) (root 5) 2 6 :=
  of_native_maps core5288 DegreeTwoThreeSpectrum4566.graph DegreeTwoThreeSpectrum3902.graph
    sourceMap5288 fusedMap5288 sourceMap5288_checked fusedMap5288_checked
    DegreeTwoThreeFiniteComparisons.comparison5288
#print axioms sourceMap5288_checked
#print axioms fusedMap5288_checked
#print axioms certified5288
def sourceMap5288swap : (Vertices 5 ⊕ Fin 7 ⊕ Fin 3) → Fin 16 :=
  fun v => ![2,6,7,8,9,10,1,0,11,12,13,14,15,3,4,5] (sourceLabel 5 6 2 v)
def fusedMap5288swap : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15] (fusedLabel 5 6 2 v)
theorem sourceMap5288swap_checked : acceptsGraphIso
    (source (graph core5288) (root 5) 6 2) DegreeTwoThreeSpectrum4566.graph sourceMap5288swap=true := by decide +kernel
theorem fusedMap5288swap_checked : acceptsGraphIso
    (fused (graph core5288) (root 5) 6 2) DegreeTwoThreeSpectrum3902.graph fusedMap5288swap=true := by decide +kernel
theorem certified5288swap : Certified (graph core5288) (root 5) 6 2 :=
  of_native_maps core5288 DegreeTwoThreeSpectrum4566.graph DegreeTwoThreeSpectrum3902.graph
    sourceMap5288swap fusedMap5288swap sourceMap5288swap_checked fusedMap5288swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5288
#print axioms sourceMap5288swap_checked
#print axioms fusedMap5288swap_checked
#print axioms certified5288swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
