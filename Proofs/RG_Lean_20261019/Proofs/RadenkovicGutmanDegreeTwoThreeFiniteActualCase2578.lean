/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2578 : Family 10 := level10.get ⟨464,by decide⟩
def sourceMap2578 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2578 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (fusedLabel 10 0 4 v)
theorem sourceMap2578_checked : acceptsGraphIso
    (source (graph core2578) (root 10) 0 4) DegreeTwoThreeSpectrum5903.graph sourceMap2578=true := by decide +kernel
theorem fusedMap2578_checked : acceptsGraphIso
    (fused (graph core2578) (root 10) 0 4) DegreeTwoThreeSpectrum5907.graph fusedMap2578=true := by decide +kernel
theorem certified2578 : Certified (graph core2578) (root 10) 0 4 :=
  of_native_maps core2578 DegreeTwoThreeSpectrum5903.graph DegreeTwoThreeSpectrum5907.graph
    sourceMap2578 fusedMap2578 sourceMap2578_checked fusedMap2578_checked
    DegreeTwoThreeFiniteComparisons.comparison2578
#print axioms sourceMap2578_checked
#print axioms fusedMap2578_checked
#print axioms certified2578
def sourceMap2578swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2578swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (fusedLabel 10 4 0 v)
theorem sourceMap2578swap_checked : acceptsGraphIso
    (source (graph core2578) (root 10) 4 0) DegreeTwoThreeSpectrum5903.graph sourceMap2578swap=true := by decide +kernel
theorem fusedMap2578swap_checked : acceptsGraphIso
    (fused (graph core2578) (root 10) 4 0) DegreeTwoThreeSpectrum5907.graph fusedMap2578swap=true := by decide +kernel
theorem certified2578swap : Certified (graph core2578) (root 10) 4 0 :=
  of_native_maps core2578 DegreeTwoThreeSpectrum5903.graph DegreeTwoThreeSpectrum5907.graph
    sourceMap2578swap fusedMap2578swap sourceMap2578swap_checked fusedMap2578swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2578
#print axioms sourceMap2578swap_checked
#print axioms fusedMap2578swap_checked
#print axioms certified2578swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
