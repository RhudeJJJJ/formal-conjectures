/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2664 : Family 10 := level10.get ⟨719,by decide⟩
def sourceMap2664 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2664 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2664_checked : acceptsGraphIso
    (source (graph core2664) (root 10) 0 4) DegreeTwoThreeSpectrum6574.graph sourceMap2664=true := by decide +kernel
theorem fusedMap2664_checked : acceptsGraphIso
    (fused (graph core2664) (root 10) 0 4) DegreeTwoThreeSpectrum5466.graph fusedMap2664=true := by decide +kernel
theorem certified2664 : Certified (graph core2664) (root 10) 0 4 :=
  of_native_maps core2664 DegreeTwoThreeSpectrum6574.graph DegreeTwoThreeSpectrum5466.graph
    sourceMap2664 fusedMap2664 sourceMap2664_checked fusedMap2664_checked
    DegreeTwoThreeFiniteComparisons.comparison2664
#print axioms sourceMap2664_checked
#print axioms fusedMap2664_checked
#print axioms certified2664
def sourceMap2664swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2664swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2664swap_checked : acceptsGraphIso
    (source (graph core2664) (root 10) 4 0) DegreeTwoThreeSpectrum6574.graph sourceMap2664swap=true := by decide +kernel
theorem fusedMap2664swap_checked : acceptsGraphIso
    (fused (graph core2664) (root 10) 4 0) DegreeTwoThreeSpectrum5466.graph fusedMap2664swap=true := by decide +kernel
theorem certified2664swap : Certified (graph core2664) (root 10) 4 0 :=
  of_native_maps core2664 DegreeTwoThreeSpectrum6574.graph DegreeTwoThreeSpectrum5466.graph
    sourceMap2664swap fusedMap2664swap sourceMap2664swap_checked fusedMap2664swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2664
#print axioms sourceMap2664swap_checked
#print axioms fusedMap2664swap_checked
#print axioms certified2664swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
