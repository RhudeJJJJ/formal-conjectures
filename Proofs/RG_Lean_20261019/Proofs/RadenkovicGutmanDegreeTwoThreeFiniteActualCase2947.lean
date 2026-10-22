/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2947 : Family 10 := level10.get ⟨1430,by decide⟩
def sourceMap2947 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2947 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2947_checked : acceptsGraphIso
    (source (graph core2947) (root 10) 0 4) DegreeTwoThreeSpectrum6885.graph sourceMap2947=true := by decide +kernel
theorem fusedMap2947_checked : acceptsGraphIso
    (fused (graph core2947) (root 10) 0 4) DegreeTwoThreeSpectrum6886.graph fusedMap2947=true := by decide +kernel
theorem certified2947 : Certified (graph core2947) (root 10) 0 4 :=
  of_native_maps core2947 DegreeTwoThreeSpectrum6885.graph DegreeTwoThreeSpectrum6886.graph
    sourceMap2947 fusedMap2947 sourceMap2947_checked fusedMap2947_checked
    DegreeTwoThreeFiniteComparisons.comparison2947
#print axioms sourceMap2947_checked
#print axioms fusedMap2947_checked
#print axioms certified2947
def sourceMap2947swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2947swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2947swap_checked : acceptsGraphIso
    (source (graph core2947) (root 10) 4 0) DegreeTwoThreeSpectrum6885.graph sourceMap2947swap=true := by decide +kernel
theorem fusedMap2947swap_checked : acceptsGraphIso
    (fused (graph core2947) (root 10) 4 0) DegreeTwoThreeSpectrum6886.graph fusedMap2947swap=true := by decide +kernel
theorem certified2947swap : Certified (graph core2947) (root 10) 4 0 :=
  of_native_maps core2947 DegreeTwoThreeSpectrum6885.graph DegreeTwoThreeSpectrum6886.graph
    sourceMap2947swap fusedMap2947swap sourceMap2947swap_checked fusedMap2947swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2947
#print axioms sourceMap2947swap_checked
#print axioms fusedMap2947swap_checked
#print axioms certified2947swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
