/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2684 : Family 10 := level10.get ⟨778,by decide⟩
def sourceMap2684 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2684 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2684_checked : acceptsGraphIso
    (source (graph core2684) (root 10) 0 4) DegreeTwoThreeSpectrum6712.graph sourceMap2684=true := by decide +kernel
theorem fusedMap2684_checked : acceptsGraphIso
    (fused (graph core2684) (root 10) 0 4) DegreeTwoThreeSpectrum5557.graph fusedMap2684=true := by decide +kernel
theorem certified2684 : Certified (graph core2684) (root 10) 0 4 :=
  of_native_maps core2684 DegreeTwoThreeSpectrum6712.graph DegreeTwoThreeSpectrum5557.graph
    sourceMap2684 fusedMap2684 sourceMap2684_checked fusedMap2684_checked
    DegreeTwoThreeFiniteComparisons.comparison2684
#print axioms sourceMap2684_checked
#print axioms fusedMap2684_checked
#print axioms certified2684
def sourceMap2684swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2684swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2684swap_checked : acceptsGraphIso
    (source (graph core2684) (root 10) 4 0) DegreeTwoThreeSpectrum6712.graph sourceMap2684swap=true := by decide +kernel
theorem fusedMap2684swap_checked : acceptsGraphIso
    (fused (graph core2684) (root 10) 4 0) DegreeTwoThreeSpectrum5557.graph fusedMap2684swap=true := by decide +kernel
theorem certified2684swap : Certified (graph core2684) (root 10) 4 0 :=
  of_native_maps core2684 DegreeTwoThreeSpectrum6712.graph DegreeTwoThreeSpectrum5557.graph
    sourceMap2684swap fusedMap2684swap sourceMap2684swap_checked fusedMap2684swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2684
#print axioms sourceMap2684swap_checked
#print axioms fusedMap2684swap_checked
#print axioms certified2684swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
