/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2962 : Family 10 := level10.get ⟨1462,by decide⟩
def sourceMap2962 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2962 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2962_checked : acceptsGraphIso
    (source (graph core2962) (root 10) 0 4) DegreeTwoThreeSpectrum6937.graph sourceMap2962=true := by decide +kernel
theorem fusedMap2962_checked : acceptsGraphIso
    (fused (graph core2962) (root 10) 0 4) DegreeTwoThreeSpectrum6938.graph fusedMap2962=true := by decide +kernel
theorem certified2962 : Certified (graph core2962) (root 10) 0 4 :=
  of_native_maps core2962 DegreeTwoThreeSpectrum6937.graph DegreeTwoThreeSpectrum6938.graph
    sourceMap2962 fusedMap2962 sourceMap2962_checked fusedMap2962_checked
    DegreeTwoThreeFiniteComparisons.comparison2962
#print axioms sourceMap2962_checked
#print axioms fusedMap2962_checked
#print axioms certified2962
def sourceMap2962swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2962swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2962swap_checked : acceptsGraphIso
    (source (graph core2962) (root 10) 4 0) DegreeTwoThreeSpectrum6937.graph sourceMap2962swap=true := by decide +kernel
theorem fusedMap2962swap_checked : acceptsGraphIso
    (fused (graph core2962) (root 10) 4 0) DegreeTwoThreeSpectrum6938.graph fusedMap2962swap=true := by decide +kernel
theorem certified2962swap : Certified (graph core2962) (root 10) 4 0 :=
  of_native_maps core2962 DegreeTwoThreeSpectrum6937.graph DegreeTwoThreeSpectrum6938.graph
    sourceMap2962swap fusedMap2962swap sourceMap2962swap_checked fusedMap2962swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2962
#print axioms sourceMap2962swap_checked
#print axioms fusedMap2962swap_checked
#print axioms certified2962swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
