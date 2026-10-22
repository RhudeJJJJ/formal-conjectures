/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2653 : Family 10 := level10.get ⟨686,by decide⟩
def sourceMap2653 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2653 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2653_checked : acceptsGraphIso
    (source (graph core2653) (root 10) 0 4) DegreeTwoThreeSpectrum6485.graph sourceMap2653=true := by decide +kernel
theorem fusedMap2653_checked : acceptsGraphIso
    (fused (graph core2653) (root 10) 0 4) DegreeTwoThreeSpectrum5423.graph fusedMap2653=true := by decide +kernel
theorem certified2653 : Certified (graph core2653) (root 10) 0 4 :=
  of_native_maps core2653 DegreeTwoThreeSpectrum6485.graph DegreeTwoThreeSpectrum5423.graph
    sourceMap2653 fusedMap2653 sourceMap2653_checked fusedMap2653_checked
    DegreeTwoThreeFiniteComparisons.comparison2653
#print axioms sourceMap2653_checked
#print axioms fusedMap2653_checked
#print axioms certified2653
def sourceMap2653swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2653swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2653swap_checked : acceptsGraphIso
    (source (graph core2653) (root 10) 4 0) DegreeTwoThreeSpectrum6485.graph sourceMap2653swap=true := by decide +kernel
theorem fusedMap2653swap_checked : acceptsGraphIso
    (fused (graph core2653) (root 10) 4 0) DegreeTwoThreeSpectrum5423.graph fusedMap2653swap=true := by decide +kernel
theorem certified2653swap : Certified (graph core2653) (root 10) 4 0 :=
  of_native_maps core2653 DegreeTwoThreeSpectrum6485.graph DegreeTwoThreeSpectrum5423.graph
    sourceMap2653swap fusedMap2653swap sourceMap2653swap_checked fusedMap2653swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2653
#print axioms sourceMap2653swap_checked
#print axioms fusedMap2653swap_checked
#print axioms certified2653swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
