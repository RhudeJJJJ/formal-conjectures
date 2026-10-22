/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2095 : Family 7 := level7.get ⟨48,by decide⟩
def sourceMap2095 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 7 0 4 v)
def fusedMap2095 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 0 4 v)
theorem sourceMap2095_checked : acceptsGraphIso
    (source (graph core2095) (root 7) 0 4) DegreeTwoThreeSpectrum1843.graph sourceMap2095=true := by decide +kernel
theorem fusedMap2095_checked : acceptsGraphIso
    (fused (graph core2095) (root 7) 0 4) DegreeTwoThreeSpectrum1845.graph fusedMap2095=true := by decide +kernel
theorem certified2095 : Certified (graph core2095) (root 7) 0 4 :=
  of_native_maps core2095 DegreeTwoThreeSpectrum1843.graph DegreeTwoThreeSpectrum1845.graph
    sourceMap2095 fusedMap2095 sourceMap2095_checked fusedMap2095_checked
    DegreeTwoThreeFiniteComparisons.comparison2095
#print axioms sourceMap2095_checked
#print axioms fusedMap2095_checked
#print axioms certified2095
def sourceMap2095swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,12,13,8] (sourceLabel 7 4 0 v)
def fusedMap2095swap : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 4 0 v)
theorem sourceMap2095swap_checked : acceptsGraphIso
    (source (graph core2095) (root 7) 4 0) DegreeTwoThreeSpectrum1843.graph sourceMap2095swap=true := by decide +kernel
theorem fusedMap2095swap_checked : acceptsGraphIso
    (fused (graph core2095) (root 7) 4 0) DegreeTwoThreeSpectrum1845.graph fusedMap2095swap=true := by decide +kernel
theorem certified2095swap : Certified (graph core2095) (root 7) 4 0 :=
  of_native_maps core2095 DegreeTwoThreeSpectrum1843.graph DegreeTwoThreeSpectrum1845.graph
    sourceMap2095swap fusedMap2095swap sourceMap2095swap_checked fusedMap2095swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2095
#print axioms sourceMap2095swap_checked
#print axioms fusedMap2095swap_checked
#print axioms certified2095swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
