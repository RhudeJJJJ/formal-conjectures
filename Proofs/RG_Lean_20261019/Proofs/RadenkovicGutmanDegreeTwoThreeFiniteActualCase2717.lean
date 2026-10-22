/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2717 : Family 10 := level10.get ⟨868,by decide⟩
def sourceMap2717 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2717 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2717_checked : acceptsGraphIso
    (source (graph core2717) (root 10) 0 4) DegreeTwoThreeSpectrum6927.graph sourceMap2717=true := by decide +kernel
theorem fusedMap2717_checked : acceptsGraphIso
    (fused (graph core2717) (root 10) 0 4) DegreeTwoThreeSpectrum5708.graph fusedMap2717=true := by decide +kernel
theorem certified2717 : Certified (graph core2717) (root 10) 0 4 :=
  of_native_maps core2717 DegreeTwoThreeSpectrum6927.graph DegreeTwoThreeSpectrum5708.graph
    sourceMap2717 fusedMap2717 sourceMap2717_checked fusedMap2717_checked
    DegreeTwoThreeFiniteComparisons.comparison2717
#print axioms sourceMap2717_checked
#print axioms fusedMap2717_checked
#print axioms certified2717
def sourceMap2717swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2717swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2717swap_checked : acceptsGraphIso
    (source (graph core2717) (root 10) 4 0) DegreeTwoThreeSpectrum6927.graph sourceMap2717swap=true := by decide +kernel
theorem fusedMap2717swap_checked : acceptsGraphIso
    (fused (graph core2717) (root 10) 4 0) DegreeTwoThreeSpectrum5708.graph fusedMap2717swap=true := by decide +kernel
theorem certified2717swap : Certified (graph core2717) (root 10) 4 0 :=
  of_native_maps core2717 DegreeTwoThreeSpectrum6927.graph DegreeTwoThreeSpectrum5708.graph
    sourceMap2717swap fusedMap2717swap sourceMap2717swap_checked fusedMap2717swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2717
#print axioms sourceMap2717swap_checked
#print axioms fusedMap2717swap_checked
#print axioms certified2717swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
