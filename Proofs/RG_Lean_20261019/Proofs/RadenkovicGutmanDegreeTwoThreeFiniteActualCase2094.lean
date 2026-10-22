/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2094 : Family 7 := level7.get ⟨47,by decide⟩
def sourceMap2094 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 7 0 4 v)
def fusedMap2094 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 0 4 v)
theorem sourceMap2094_checked : acceptsGraphIso
    (source (graph core2094) (root 7) 0 4) DegreeTwoThreeSpectrum1837.graph sourceMap2094=true := by decide +kernel
theorem fusedMap2094_checked : acceptsGraphIso
    (fused (graph core2094) (root 7) 0 4) DegreeTwoThreeSpectrum1839.graph fusedMap2094=true := by decide +kernel
theorem certified2094 : Certified (graph core2094) (root 7) 0 4 :=
  of_native_maps core2094 DegreeTwoThreeSpectrum1837.graph DegreeTwoThreeSpectrum1839.graph
    sourceMap2094 fusedMap2094 sourceMap2094_checked fusedMap2094_checked
    DegreeTwoThreeFiniteComparisons.comparison2094
#print axioms sourceMap2094_checked
#print axioms fusedMap2094_checked
#print axioms certified2094
def sourceMap2094swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,12,13,8] (sourceLabel 7 4 0 v)
def fusedMap2094swap : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 4 0 v)
theorem sourceMap2094swap_checked : acceptsGraphIso
    (source (graph core2094) (root 7) 4 0) DegreeTwoThreeSpectrum1837.graph sourceMap2094swap=true := by decide +kernel
theorem fusedMap2094swap_checked : acceptsGraphIso
    (fused (graph core2094) (root 7) 4 0) DegreeTwoThreeSpectrum1839.graph fusedMap2094swap=true := by decide +kernel
theorem certified2094swap : Certified (graph core2094) (root 7) 4 0 :=
  of_native_maps core2094 DegreeTwoThreeSpectrum1837.graph DegreeTwoThreeSpectrum1839.graph
    sourceMap2094swap fusedMap2094swap sourceMap2094swap_checked fusedMap2094swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2094
#print axioms sourceMap2094swap_checked
#print axioms fusedMap2094swap_checked
#print axioms certified2094swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
