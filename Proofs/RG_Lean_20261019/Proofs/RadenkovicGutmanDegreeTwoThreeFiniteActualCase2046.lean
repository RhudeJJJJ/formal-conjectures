/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2046 : Family 10 := level10.get ⟨1768,by decide⟩
def sourceMap2046 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,8,9,10,11,12,13,14,5,6,7] (sourceLabel 10 0 2 v)
def fusedMap2046 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2046_checked : acceptsGraphIso
    (source (graph core2046) (root 10) 0 2) DegreeTwoThreeSpectrum3848.graph sourceMap2046=true := by decide +kernel
theorem fusedMap2046_checked : acceptsGraphIso
    (fused (graph core2046) (root 10) 0 2) DegreeTwoThreeSpectrum3542.graph fusedMap2046=true := by decide +kernel
theorem certified2046 : Certified (graph core2046) (root 10) 0 2 :=
  of_native_maps core2046 DegreeTwoThreeSpectrum3848.graph DegreeTwoThreeSpectrum3542.graph
    sourceMap2046 fusedMap2046 sourceMap2046_checked fusedMap2046_checked
    DegreeTwoThreeFiniteComparisons.comparison2046
#print axioms sourceMap2046_checked
#print axioms fusedMap2046_checked
#print axioms certified2046
def sourceMap2046swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,8,9,10,11,12,13,5,6,7,14] (sourceLabel 10 2 0 v)
def fusedMap2046swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2046swap_checked : acceptsGraphIso
    (source (graph core2046) (root 10) 2 0) DegreeTwoThreeSpectrum3848.graph sourceMap2046swap=true := by decide +kernel
theorem fusedMap2046swap_checked : acceptsGraphIso
    (fused (graph core2046) (root 10) 2 0) DegreeTwoThreeSpectrum3542.graph fusedMap2046swap=true := by decide +kernel
theorem certified2046swap : Certified (graph core2046) (root 10) 2 0 :=
  of_native_maps core2046 DegreeTwoThreeSpectrum3848.graph DegreeTwoThreeSpectrum3542.graph
    sourceMap2046swap fusedMap2046swap sourceMap2046swap_checked fusedMap2046swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2046
#print axioms sourceMap2046swap_checked
#print axioms fusedMap2046swap_checked
#print axioms certified2046swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
