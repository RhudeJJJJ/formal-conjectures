/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2723 : Family 10 := level10.get ⟨881,by decide⟩
def sourceMap2723 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2723 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2723_checked : acceptsGraphIso
    (source (graph core2723) (root 10) 0 4) DegreeTwoThreeSpectrum6943.graph sourceMap2723=true := by decide +kernel
theorem fusedMap2723_checked : acceptsGraphIso
    (fused (graph core2723) (root 10) 0 4) DegreeTwoThreeSpectrum5732.graph fusedMap2723=true := by decide +kernel
theorem certified2723 : Certified (graph core2723) (root 10) 0 4 :=
  of_native_maps core2723 DegreeTwoThreeSpectrum6943.graph DegreeTwoThreeSpectrum5732.graph
    sourceMap2723 fusedMap2723 sourceMap2723_checked fusedMap2723_checked
    DegreeTwoThreeFiniteComparisons.comparison2723
#print axioms sourceMap2723_checked
#print axioms fusedMap2723_checked
#print axioms certified2723
def sourceMap2723swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2723swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2723swap_checked : acceptsGraphIso
    (source (graph core2723) (root 10) 4 0) DegreeTwoThreeSpectrum6943.graph sourceMap2723swap=true := by decide +kernel
theorem fusedMap2723swap_checked : acceptsGraphIso
    (fused (graph core2723) (root 10) 4 0) DegreeTwoThreeSpectrum5732.graph fusedMap2723swap=true := by decide +kernel
theorem certified2723swap : Certified (graph core2723) (root 10) 4 0 :=
  of_native_maps core2723 DegreeTwoThreeSpectrum6943.graph DegreeTwoThreeSpectrum5732.graph
    sourceMap2723swap fusedMap2723swap sourceMap2723swap_checked fusedMap2723swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2723
#print axioms sourceMap2723swap_checked
#print axioms fusedMap2723swap_checked
#print axioms certified2723swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
