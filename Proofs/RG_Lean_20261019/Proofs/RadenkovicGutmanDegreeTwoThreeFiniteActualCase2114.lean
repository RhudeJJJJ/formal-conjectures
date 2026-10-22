/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2114 : Family 7 := level7.get ⟨91,by decide⟩
def sourceMap2114 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13] (sourceLabel 7 0 4 v)
def fusedMap2114 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 0 4 v)
theorem sourceMap2114_checked : acceptsGraphIso
    (source (graph core2114) (root 7) 0 4) DegreeTwoThreeSpectrum2147.graph sourceMap2114=true := by decide +kernel
theorem fusedMap2114_checked : acceptsGraphIso
    (fused (graph core2114) (root 7) 0 4) DegreeTwoThreeSpectrum1831.graph fusedMap2114=true := by decide +kernel
theorem certified2114 : Certified (graph core2114) (root 7) 0 4 :=
  of_native_maps core2114 DegreeTwoThreeSpectrum2147.graph DegreeTwoThreeSpectrum1831.graph
    sourceMap2114 fusedMap2114 sourceMap2114_checked fusedMap2114_checked
    DegreeTwoThreeFiniteComparisons.comparison2114
#print axioms sourceMap2114_checked
#print axioms fusedMap2114_checked
#print axioms certified2114
def sourceMap2114swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,9] (sourceLabel 7 4 0 v)
def fusedMap2114swap : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 4 0 v)
theorem sourceMap2114swap_checked : acceptsGraphIso
    (source (graph core2114) (root 7) 4 0) DegreeTwoThreeSpectrum2147.graph sourceMap2114swap=true := by decide +kernel
theorem fusedMap2114swap_checked : acceptsGraphIso
    (fused (graph core2114) (root 7) 4 0) DegreeTwoThreeSpectrum1831.graph fusedMap2114swap=true := by decide +kernel
theorem certified2114swap : Certified (graph core2114) (root 7) 4 0 :=
  of_native_maps core2114 DegreeTwoThreeSpectrum2147.graph DegreeTwoThreeSpectrum1831.graph
    sourceMap2114swap fusedMap2114swap sourceMap2114swap_checked fusedMap2114swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2114
#print axioms sourceMap2114swap_checked
#print axioms fusedMap2114swap_checked
#print axioms certified2114swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
