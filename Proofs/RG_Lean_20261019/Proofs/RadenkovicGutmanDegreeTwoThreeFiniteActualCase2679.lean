/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2679 : Family 10 := level10.get ⟨760,by decide⟩
def sourceMap2679 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2679 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2679_checked : acceptsGraphIso
    (source (graph core2679) (root 10) 0 4) DegreeTwoThreeSpectrum6672.graph sourceMap2679=true := by decide +kernel
theorem fusedMap2679_checked : acceptsGraphIso
    (fused (graph core2679) (root 10) 0 4) DegreeTwoThreeSpectrum5530.graph fusedMap2679=true := by decide +kernel
theorem certified2679 : Certified (graph core2679) (root 10) 0 4 :=
  of_native_maps core2679 DegreeTwoThreeSpectrum6672.graph DegreeTwoThreeSpectrum5530.graph
    sourceMap2679 fusedMap2679 sourceMap2679_checked fusedMap2679_checked
    DegreeTwoThreeFiniteComparisons.comparison2679
#print axioms sourceMap2679_checked
#print axioms fusedMap2679_checked
#print axioms certified2679
def sourceMap2679swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2679swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2679swap_checked : acceptsGraphIso
    (source (graph core2679) (root 10) 4 0) DegreeTwoThreeSpectrum6672.graph sourceMap2679swap=true := by decide +kernel
theorem fusedMap2679swap_checked : acceptsGraphIso
    (fused (graph core2679) (root 10) 4 0) DegreeTwoThreeSpectrum5530.graph fusedMap2679swap=true := by decide +kernel
theorem certified2679swap : Certified (graph core2679) (root 10) 4 0 :=
  of_native_maps core2679 DegreeTwoThreeSpectrum6672.graph DegreeTwoThreeSpectrum5530.graph
    sourceMap2679swap fusedMap2679swap sourceMap2679swap_checked fusedMap2679swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2679
#print axioms sourceMap2679swap_checked
#print axioms fusedMap2679swap_checked
#print axioms certified2679swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
