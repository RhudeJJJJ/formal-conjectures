/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3253 : Family 9 := level9.get ⟨87,by decide⟩
def sourceMap3253 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 9 0 5 v)
def fusedMap3253 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3253_checked : acceptsGraphIso
    (source (graph core3253) (root 9) 0 5) DegreeTwoThreeSpectrum5629.graph sourceMap3253=true := by decide +kernel
theorem fusedMap3253_checked : acceptsGraphIso
    (fused (graph core3253) (root 9) 0 5) DegreeTwoThreeSpectrum5031.graph fusedMap3253=true := by decide +kernel
theorem certified3253 : Certified (graph core3253) (root 9) 0 5 :=
  of_native_maps core3253 DegreeTwoThreeSpectrum5629.graph DegreeTwoThreeSpectrum5031.graph
    sourceMap3253 fusedMap3253 sourceMap3253_checked fusedMap3253_checked
    DegreeTwoThreeFiniteComparisons.comparison3253
#print axioms sourceMap3253_checked
#print axioms fusedMap3253_checked
#print axioms certified3253
def sourceMap3253swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14,16] (sourceLabel 9 5 0 v)
def fusedMap3253swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3253swap_checked : acceptsGraphIso
    (source (graph core3253) (root 9) 5 0) DegreeTwoThreeSpectrum5629.graph sourceMap3253swap=true := by decide +kernel
theorem fusedMap3253swap_checked : acceptsGraphIso
    (fused (graph core3253) (root 9) 5 0) DegreeTwoThreeSpectrum5031.graph fusedMap3253swap=true := by decide +kernel
theorem certified3253swap : Certified (graph core3253) (root 9) 5 0 :=
  of_native_maps core3253 DegreeTwoThreeSpectrum5629.graph DegreeTwoThreeSpectrum5031.graph
    sourceMap3253swap fusedMap3253swap sourceMap3253swap_checked fusedMap3253swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3253
#print axioms sourceMap3253swap_checked
#print axioms fusedMap3253swap_checked
#print axioms certified3253swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
