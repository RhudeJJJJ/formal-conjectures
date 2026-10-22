/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2834 : Family 10 := level10.get ⟨1162,by decide⟩
def sourceMap2834 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2834 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2834_checked : acceptsGraphIso
    (source (graph core2834) (root 10) 0 4) DegreeTwoThreeSpectrum6307.graph sourceMap2834=true := by decide +kernel
theorem fusedMap2834_checked : acceptsGraphIso
    (fused (graph core2834) (root 10) 0 4) DegreeTwoThreeSpectrum6308.graph fusedMap2834=true := by decide +kernel
theorem certified2834 : Certified (graph core2834) (root 10) 0 4 :=
  of_native_maps core2834 DegreeTwoThreeSpectrum6307.graph DegreeTwoThreeSpectrum6308.graph
    sourceMap2834 fusedMap2834 sourceMap2834_checked fusedMap2834_checked
    DegreeTwoThreeFiniteComparisons.comparison2834
#print axioms sourceMap2834_checked
#print axioms fusedMap2834_checked
#print axioms certified2834
def sourceMap2834swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2834swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2834swap_checked : acceptsGraphIso
    (source (graph core2834) (root 10) 4 0) DegreeTwoThreeSpectrum6307.graph sourceMap2834swap=true := by decide +kernel
theorem fusedMap2834swap_checked : acceptsGraphIso
    (fused (graph core2834) (root 10) 4 0) DegreeTwoThreeSpectrum6308.graph fusedMap2834swap=true := by decide +kernel
theorem certified2834swap : Certified (graph core2834) (root 10) 4 0 :=
  of_native_maps core2834 DegreeTwoThreeSpectrum6307.graph DegreeTwoThreeSpectrum6308.graph
    sourceMap2834swap fusedMap2834swap sourceMap2834swap_checked fusedMap2834swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2834
#print axioms sourceMap2834swap_checked
#print axioms fusedMap2834swap_checked
#print axioms certified2834swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
