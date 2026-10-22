/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2600 : Family 10 := level10.get ⟨532,by decide⟩
def sourceMap2600 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2600 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2600_checked : acceptsGraphIso
    (source (graph core2600) (root 10) 0 4) DegreeTwoThreeSpectrum6113.graph sourceMap2600=true := by decide +kernel
theorem fusedMap2600_checked : acceptsGraphIso
    (fused (graph core2600) (root 10) 0 4) DegreeTwoThreeSpectrum5178.graph fusedMap2600=true := by decide +kernel
theorem certified2600 : Certified (graph core2600) (root 10) 0 4 :=
  of_native_maps core2600 DegreeTwoThreeSpectrum6113.graph DegreeTwoThreeSpectrum5178.graph
    sourceMap2600 fusedMap2600 sourceMap2600_checked fusedMap2600_checked
    DegreeTwoThreeFiniteComparisons.comparison2600
#print axioms sourceMap2600_checked
#print axioms fusedMap2600_checked
#print axioms certified2600
def sourceMap2600swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2600swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2600swap_checked : acceptsGraphIso
    (source (graph core2600) (root 10) 4 0) DegreeTwoThreeSpectrum6113.graph sourceMap2600swap=true := by decide +kernel
theorem fusedMap2600swap_checked : acceptsGraphIso
    (fused (graph core2600) (root 10) 4 0) DegreeTwoThreeSpectrum5178.graph fusedMap2600swap=true := by decide +kernel
theorem certified2600swap : Certified (graph core2600) (root 10) 4 0 :=
  of_native_maps core2600 DegreeTwoThreeSpectrum6113.graph DegreeTwoThreeSpectrum5178.graph
    sourceMap2600swap fusedMap2600swap sourceMap2600swap_checked fusedMap2600swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2600
#print axioms sourceMap2600swap_checked
#print axioms fusedMap2600swap_checked
#print axioms certified2600swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
