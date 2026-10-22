/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3265 : Family 9 := level9.get ⟨128,by decide⟩
def sourceMap3265 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 9 0 5 v)
def fusedMap3265 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3265_checked : acceptsGraphIso
    (source (graph core3265) (root 9) 0 5) DegreeTwoThreeSpectrum5943.graph sourceMap3265=true := by decide +kernel
theorem fusedMap3265_checked : acceptsGraphIso
    (fused (graph core3265) (root 9) 0 5) DegreeTwoThreeSpectrum5109.graph fusedMap3265=true := by decide +kernel
theorem certified3265 : Certified (graph core3265) (root 9) 0 5 :=
  of_native_maps core3265 DegreeTwoThreeSpectrum5943.graph DegreeTwoThreeSpectrum5109.graph
    sourceMap3265 fusedMap3265 sourceMap3265_checked fusedMap3265_checked
    DegreeTwoThreeFiniteComparisons.comparison3265
#print axioms sourceMap3265_checked
#print axioms fusedMap3265_checked
#print axioms certified3265
def sourceMap3265swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14,16] (sourceLabel 9 5 0 v)
def fusedMap3265swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3265swap_checked : acceptsGraphIso
    (source (graph core3265) (root 9) 5 0) DegreeTwoThreeSpectrum5943.graph sourceMap3265swap=true := by decide +kernel
theorem fusedMap3265swap_checked : acceptsGraphIso
    (fused (graph core3265) (root 9) 5 0) DegreeTwoThreeSpectrum5109.graph fusedMap3265swap=true := by decide +kernel
theorem certified3265swap : Certified (graph core3265) (root 9) 5 0 :=
  of_native_maps core3265 DegreeTwoThreeSpectrum5943.graph DegreeTwoThreeSpectrum5109.graph
    sourceMap3265swap fusedMap3265swap sourceMap3265swap_checked fusedMap3265swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3265
#print axioms sourceMap3265swap_checked
#print axioms fusedMap3265swap_checked
#print axioms certified3265swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
