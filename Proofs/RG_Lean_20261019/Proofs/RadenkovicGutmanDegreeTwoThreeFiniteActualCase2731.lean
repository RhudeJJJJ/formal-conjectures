/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2731 : Family 10 := level10.get ⟨905,by decide⟩
def sourceMap2731 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2731 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2731_checked : acceptsGraphIso
    (source (graph core2731) (root 10) 0 4) DegreeTwoThreeSpectrum6981.graph sourceMap2731=true := by decide +kernel
theorem fusedMap2731_checked : acceptsGraphIso
    (fused (graph core2731) (root 10) 0 4) DegreeTwoThreeSpectrum5770.graph fusedMap2731=true := by decide +kernel
theorem certified2731 : Certified (graph core2731) (root 10) 0 4 :=
  of_native_maps core2731 DegreeTwoThreeSpectrum6981.graph DegreeTwoThreeSpectrum5770.graph
    sourceMap2731 fusedMap2731 sourceMap2731_checked fusedMap2731_checked
    DegreeTwoThreeFiniteComparisons.comparison2731
#print axioms sourceMap2731_checked
#print axioms fusedMap2731_checked
#print axioms certified2731
def sourceMap2731swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2731swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2731swap_checked : acceptsGraphIso
    (source (graph core2731) (root 10) 4 0) DegreeTwoThreeSpectrum6981.graph sourceMap2731swap=true := by decide +kernel
theorem fusedMap2731swap_checked : acceptsGraphIso
    (fused (graph core2731) (root 10) 4 0) DegreeTwoThreeSpectrum5770.graph fusedMap2731swap=true := by decide +kernel
theorem certified2731swap : Certified (graph core2731) (root 10) 4 0 :=
  of_native_maps core2731 DegreeTwoThreeSpectrum6981.graph DegreeTwoThreeSpectrum5770.graph
    sourceMap2731swap fusedMap2731swap sourceMap2731swap_checked fusedMap2731swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2731
#print axioms sourceMap2731swap_checked
#print axioms fusedMap2731swap_checked
#print axioms certified2731swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
