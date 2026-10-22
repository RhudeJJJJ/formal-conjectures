/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3627 : Family 8 := level8.get ⟨245,by decide⟩
def sourceMap3627 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3627 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3627_checked : acceptsGraphIso
    (source (graph core3627) (root 8) 0 6) DegreeTwoThreeSpectrum6630.graph sourceMap3627=true := by decide +kernel
theorem fusedMap3627_checked : acceptsGraphIso
    (fused (graph core3627) (root 8) 0 6) DegreeTwoThreeSpectrum5500.graph fusedMap3627=true := by decide +kernel
theorem certified3627 : Certified (graph core3627) (root 8) 0 6 :=
  of_native_maps core3627 DegreeTwoThreeSpectrum6630.graph DegreeTwoThreeSpectrum5500.graph
    sourceMap3627 fusedMap3627 sourceMap3627_checked fusedMap3627_checked
    DegreeTwoThreeFiniteComparisons.comparison3627
#print axioms sourceMap3627_checked
#print axioms fusedMap3627_checked
#print axioms certified3627
def sourceMap3627swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3627swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3627swap_checked : acceptsGraphIso
    (source (graph core3627) (root 8) 6 0) DegreeTwoThreeSpectrum6630.graph sourceMap3627swap=true := by decide +kernel
theorem fusedMap3627swap_checked : acceptsGraphIso
    (fused (graph core3627) (root 8) 6 0) DegreeTwoThreeSpectrum5500.graph fusedMap3627swap=true := by decide +kernel
theorem certified3627swap : Certified (graph core3627) (root 8) 6 0 :=
  of_native_maps core3627 DegreeTwoThreeSpectrum6630.graph DegreeTwoThreeSpectrum5500.graph
    sourceMap3627swap fusedMap3627swap sourceMap3627swap_checked fusedMap3627swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3627
#print axioms sourceMap3627swap_checked
#print axioms fusedMap3627swap_checked
#print axioms certified3627swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
