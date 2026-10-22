/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2675 : Family 10 := level10.get ⟨754,by decide⟩
def sourceMap2675 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2675 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2675_checked : acceptsGraphIso
    (source (graph core2675) (root 10) 0 4) DegreeTwoThreeSpectrum6664.graph sourceMap2675=true := by decide +kernel
theorem fusedMap2675_checked : acceptsGraphIso
    (fused (graph core2675) (root 10) 0 4) DegreeTwoThreeSpectrum5520.graph fusedMap2675=true := by decide +kernel
theorem certified2675 : Certified (graph core2675) (root 10) 0 4 :=
  of_native_maps core2675 DegreeTwoThreeSpectrum6664.graph DegreeTwoThreeSpectrum5520.graph
    sourceMap2675 fusedMap2675 sourceMap2675_checked fusedMap2675_checked
    DegreeTwoThreeFiniteComparisons.comparison2675
#print axioms sourceMap2675_checked
#print axioms fusedMap2675_checked
#print axioms certified2675
def sourceMap2675swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2675swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2675swap_checked : acceptsGraphIso
    (source (graph core2675) (root 10) 4 0) DegreeTwoThreeSpectrum6664.graph sourceMap2675swap=true := by decide +kernel
theorem fusedMap2675swap_checked : acceptsGraphIso
    (fused (graph core2675) (root 10) 4 0) DegreeTwoThreeSpectrum5520.graph fusedMap2675swap=true := by decide +kernel
theorem certified2675swap : Certified (graph core2675) (root 10) 4 0 :=
  of_native_maps core2675 DegreeTwoThreeSpectrum6664.graph DegreeTwoThreeSpectrum5520.graph
    sourceMap2675swap fusedMap2675swap sourceMap2675swap_checked fusedMap2675swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2675
#print axioms sourceMap2675swap_checked
#print axioms fusedMap2675swap_checked
#print axioms certified2675swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
