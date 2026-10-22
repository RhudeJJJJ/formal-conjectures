/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2994 : Family 10 := level10.get ⟨1554,by decide⟩
def sourceMap2994 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2994 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2994_checked : acceptsGraphIso
    (source (graph core2994) (root 10) 0 4) DegreeTwoThreeSpectrum7091.graph sourceMap2994=true := by decide +kernel
theorem fusedMap2994_checked : acceptsGraphIso
    (fused (graph core2994) (root 10) 0 4) DegreeTwoThreeSpectrum6010.graph fusedMap2994=true := by decide +kernel
theorem certified2994 : Certified (graph core2994) (root 10) 0 4 :=
  of_native_maps core2994 DegreeTwoThreeSpectrum7091.graph DegreeTwoThreeSpectrum6010.graph
    sourceMap2994 fusedMap2994 sourceMap2994_checked fusedMap2994_checked
    DegreeTwoThreeFiniteComparisons.comparison2994
#print axioms sourceMap2994_checked
#print axioms fusedMap2994_checked
#print axioms certified2994
def sourceMap2994swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap2994swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2994swap_checked : acceptsGraphIso
    (source (graph core2994) (root 10) 4 0) DegreeTwoThreeSpectrum7091.graph sourceMap2994swap=true := by decide +kernel
theorem fusedMap2994swap_checked : acceptsGraphIso
    (fused (graph core2994) (root 10) 4 0) DegreeTwoThreeSpectrum6010.graph fusedMap2994swap=true := by decide +kernel
theorem certified2994swap : Certified (graph core2994) (root 10) 4 0 :=
  of_native_maps core2994 DegreeTwoThreeSpectrum7091.graph DegreeTwoThreeSpectrum6010.graph
    sourceMap2994swap fusedMap2994swap sourceMap2994swap_checked fusedMap2994swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2994
#print axioms sourceMap2994swap_checked
#print axioms fusedMap2994swap_checked
#print axioms certified2994swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
