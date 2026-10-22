/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2913 : Family 10 := level10.get ⟨1350,by decide⟩
def sourceMap2913 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2913 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2913_checked : acceptsGraphIso
    (source (graph core2913) (root 10) 0 4) DegreeTwoThreeSpectrum6681.graph sourceMap2913=true := by decide +kernel
theorem fusedMap2913_checked : acceptsGraphIso
    (fused (graph core2913) (root 10) 0 4) DegreeTwoThreeSpectrum6682.graph fusedMap2913=true := by decide +kernel
theorem certified2913 : Certified (graph core2913) (root 10) 0 4 :=
  of_native_maps core2913 DegreeTwoThreeSpectrum6681.graph DegreeTwoThreeSpectrum6682.graph
    sourceMap2913 fusedMap2913 sourceMap2913_checked fusedMap2913_checked
    DegreeTwoThreeFiniteComparisons.comparison2913
#print axioms sourceMap2913_checked
#print axioms fusedMap2913_checked
#print axioms certified2913
def sourceMap2913swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2913swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2913swap_checked : acceptsGraphIso
    (source (graph core2913) (root 10) 4 0) DegreeTwoThreeSpectrum6681.graph sourceMap2913swap=true := by decide +kernel
theorem fusedMap2913swap_checked : acceptsGraphIso
    (fused (graph core2913) (root 10) 4 0) DegreeTwoThreeSpectrum6682.graph fusedMap2913swap=true := by decide +kernel
theorem certified2913swap : Certified (graph core2913) (root 10) 4 0 :=
  of_native_maps core2913 DegreeTwoThreeSpectrum6681.graph DegreeTwoThreeSpectrum6682.graph
    sourceMap2913swap fusedMap2913swap sourceMap2913swap_checked fusedMap2913swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2913
#print axioms sourceMap2913swap_checked
#print axioms fusedMap2913swap_checked
#print axioms certified2913swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
