/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2692 : Family 10 := level10.get ⟨797,by decide⟩
def sourceMap2692 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2692 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2692_checked : acceptsGraphIso
    (source (graph core2692) (root 10) 0 4) DegreeTwoThreeSpectrum6746.graph sourceMap2692=true := by decide +kernel
theorem fusedMap2692_checked : acceptsGraphIso
    (fused (graph core2692) (root 10) 0 4) DegreeTwoThreeSpectrum5586.graph fusedMap2692=true := by decide +kernel
theorem certified2692 : Certified (graph core2692) (root 10) 0 4 :=
  of_native_maps core2692 DegreeTwoThreeSpectrum6746.graph DegreeTwoThreeSpectrum5586.graph
    sourceMap2692 fusedMap2692 sourceMap2692_checked fusedMap2692_checked
    DegreeTwoThreeFiniteComparisons.comparison2692
#print axioms sourceMap2692_checked
#print axioms fusedMap2692_checked
#print axioms certified2692
def sourceMap2692swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2692swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2692swap_checked : acceptsGraphIso
    (source (graph core2692) (root 10) 4 0) DegreeTwoThreeSpectrum6746.graph sourceMap2692swap=true := by decide +kernel
theorem fusedMap2692swap_checked : acceptsGraphIso
    (fused (graph core2692) (root 10) 4 0) DegreeTwoThreeSpectrum5586.graph fusedMap2692swap=true := by decide +kernel
theorem certified2692swap : Certified (graph core2692) (root 10) 4 0 :=
  of_native_maps core2692 DegreeTwoThreeSpectrum6746.graph DegreeTwoThreeSpectrum5586.graph
    sourceMap2692swap fusedMap2692swap sourceMap2692swap_checked fusedMap2692swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2692
#print axioms sourceMap2692swap_checked
#print axioms fusedMap2692swap_checked
#print axioms certified2692swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
