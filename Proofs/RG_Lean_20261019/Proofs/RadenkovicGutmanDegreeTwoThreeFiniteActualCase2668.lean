/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2668 : Family 10 := level10.get ⟨732,by decide⟩
def sourceMap2668 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2668 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2668_checked : acceptsGraphIso
    (source (graph core2668) (root 10) 0 4) DegreeTwoThreeSpectrum6611.graph sourceMap2668=true := by decide +kernel
theorem fusedMap2668_checked : acceptsGraphIso
    (fused (graph core2668) (root 10) 0 4) DegreeTwoThreeSpectrum5488.graph fusedMap2668=true := by decide +kernel
theorem certified2668 : Certified (graph core2668) (root 10) 0 4 :=
  of_native_maps core2668 DegreeTwoThreeSpectrum6611.graph DegreeTwoThreeSpectrum5488.graph
    sourceMap2668 fusedMap2668 sourceMap2668_checked fusedMap2668_checked
    DegreeTwoThreeFiniteComparisons.comparison2668
#print axioms sourceMap2668_checked
#print axioms fusedMap2668_checked
#print axioms certified2668
def sourceMap2668swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2668swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2668swap_checked : acceptsGraphIso
    (source (graph core2668) (root 10) 4 0) DegreeTwoThreeSpectrum6611.graph sourceMap2668swap=true := by decide +kernel
theorem fusedMap2668swap_checked : acceptsGraphIso
    (fused (graph core2668) (root 10) 4 0) DegreeTwoThreeSpectrum5488.graph fusedMap2668swap=true := by decide +kernel
theorem certified2668swap : Certified (graph core2668) (root 10) 4 0 :=
  of_native_maps core2668 DegreeTwoThreeSpectrum6611.graph DegreeTwoThreeSpectrum5488.graph
    sourceMap2668swap fusedMap2668swap sourceMap2668swap_checked fusedMap2668swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2668
#print axioms sourceMap2668swap_checked
#print axioms fusedMap2668swap_checked
#print axioms certified2668swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
