/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3259 : Family 9 := level9.get ⟨109,by decide⟩
def sourceMap3259 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 9 0 5 v)
def fusedMap3259 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3259_checked : acceptsGraphIso
    (source (graph core3259) (root 9) 0 5) DegreeTwoThreeSpectrum5810.graph sourceMap3259=true := by decide +kernel
theorem fusedMap3259_checked : acceptsGraphIso
    (fused (graph core3259) (root 9) 0 5) DegreeTwoThreeSpectrum5069.graph fusedMap3259=true := by decide +kernel
theorem certified3259 : Certified (graph core3259) (root 9) 0 5 :=
  of_native_maps core3259 DegreeTwoThreeSpectrum5810.graph DegreeTwoThreeSpectrum5069.graph
    sourceMap3259 fusedMap3259 sourceMap3259_checked fusedMap3259_checked
    DegreeTwoThreeFiniteComparisons.comparison3259
#print axioms sourceMap3259_checked
#print axioms fusedMap3259_checked
#print axioms certified3259
def sourceMap3259swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14,16] (sourceLabel 9 5 0 v)
def fusedMap3259swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3259swap_checked : acceptsGraphIso
    (source (graph core3259) (root 9) 5 0) DegreeTwoThreeSpectrum5810.graph sourceMap3259swap=true := by decide +kernel
theorem fusedMap3259swap_checked : acceptsGraphIso
    (fused (graph core3259) (root 9) 5 0) DegreeTwoThreeSpectrum5069.graph fusedMap3259swap=true := by decide +kernel
theorem certified3259swap : Certified (graph core3259) (root 9) 5 0 :=
  of_native_maps core3259 DegreeTwoThreeSpectrum5810.graph DegreeTwoThreeSpectrum5069.graph
    sourceMap3259swap fusedMap3259swap sourceMap3259swap_checked fusedMap3259swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3259
#print axioms sourceMap3259swap_checked
#print axioms fusedMap3259swap_checked
#print axioms certified3259swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
