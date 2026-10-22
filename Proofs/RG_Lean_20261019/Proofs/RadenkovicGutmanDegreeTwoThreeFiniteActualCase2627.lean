/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2627 : Family 10 := level10.get ⟨612,by decide⟩
def sourceMap2627 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2627 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2627_checked : acceptsGraphIso
    (source (graph core2627) (root 10) 0 4) DegreeTwoThreeSpectrum6334.graph sourceMap2627=true := by decide +kernel
theorem fusedMap2627_checked : acceptsGraphIso
    (fused (graph core2627) (root 10) 0 4) DegreeTwoThreeSpectrum5295.graph fusedMap2627=true := by decide +kernel
theorem certified2627 : Certified (graph core2627) (root 10) 0 4 :=
  of_native_maps core2627 DegreeTwoThreeSpectrum6334.graph DegreeTwoThreeSpectrum5295.graph
    sourceMap2627 fusedMap2627 sourceMap2627_checked fusedMap2627_checked
    DegreeTwoThreeFiniteComparisons.comparison2627
#print axioms sourceMap2627_checked
#print axioms fusedMap2627_checked
#print axioms certified2627
def sourceMap2627swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2627swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2627swap_checked : acceptsGraphIso
    (source (graph core2627) (root 10) 4 0) DegreeTwoThreeSpectrum6334.graph sourceMap2627swap=true := by decide +kernel
theorem fusedMap2627swap_checked : acceptsGraphIso
    (fused (graph core2627) (root 10) 4 0) DegreeTwoThreeSpectrum5295.graph fusedMap2627swap=true := by decide +kernel
theorem certified2627swap : Certified (graph core2627) (root 10) 4 0 :=
  of_native_maps core2627 DegreeTwoThreeSpectrum6334.graph DegreeTwoThreeSpectrum5295.graph
    sourceMap2627swap fusedMap2627swap sourceMap2627swap_checked fusedMap2627swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2627
#print axioms sourceMap2627swap_checked
#print axioms fusedMap2627swap_checked
#print axioms certified2627swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
