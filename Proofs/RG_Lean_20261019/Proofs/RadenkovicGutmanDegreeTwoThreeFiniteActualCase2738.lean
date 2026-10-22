/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2738 : Family 10 := level10.get ⟨917,by decide⟩
def sourceMap2738 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,16,7,8,9,10,11] (sourceLabel 10 0 4 v)
def fusedMap2738 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2738_checked : acceptsGraphIso
    (source (graph core2738) (root 10) 0 4) DegreeTwoThreeSpectrum6989.graph sourceMap2738=true := by decide +kernel
theorem fusedMap2738_checked : acceptsGraphIso
    (fused (graph core2738) (root 10) 0 4) DegreeTwoThreeSpectrum5795.graph fusedMap2738=true := by decide +kernel
theorem certified2738 : Certified (graph core2738) (root 10) 0 4 :=
  of_native_maps core2738 DegreeTwoThreeSpectrum6989.graph DegreeTwoThreeSpectrum5795.graph
    sourceMap2738 fusedMap2738 sourceMap2738_checked fusedMap2738_checked
    DegreeTwoThreeFiniteComparisons.comparison2738
#print axioms sourceMap2738_checked
#print axioms fusedMap2738_checked
#print axioms certified2738
def sourceMap2738swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,7,8,9,10,11,16] (sourceLabel 10 4 0 v)
def fusedMap2738swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2738swap_checked : acceptsGraphIso
    (source (graph core2738) (root 10) 4 0) DegreeTwoThreeSpectrum6989.graph sourceMap2738swap=true := by decide +kernel
theorem fusedMap2738swap_checked : acceptsGraphIso
    (fused (graph core2738) (root 10) 4 0) DegreeTwoThreeSpectrum5795.graph fusedMap2738swap=true := by decide +kernel
theorem certified2738swap : Certified (graph core2738) (root 10) 4 0 :=
  of_native_maps core2738 DegreeTwoThreeSpectrum6989.graph DegreeTwoThreeSpectrum5795.graph
    sourceMap2738swap fusedMap2738swap sourceMap2738swap_checked fusedMap2738swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2738
#print axioms sourceMap2738swap_checked
#print axioms fusedMap2738swap_checked
#print axioms certified2738swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
