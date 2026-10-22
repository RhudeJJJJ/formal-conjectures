/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3300 : Family 9 := level9.get ⟨237,by decide⟩
def sourceMap3300 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3300 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3300_checked : acceptsGraphIso
    (source (graph core3300) (root 9) 0 5) DegreeTwoThreeSpectrum5587.graph sourceMap3300=true := by decide +kernel
theorem fusedMap3300_checked : acceptsGraphIso
    (fused (graph core3300) (root 9) 0 5) DegreeTwoThreeSpectrum5588.graph fusedMap3300=true := by decide +kernel
theorem certified3300 : Certified (graph core3300) (root 9) 0 5 :=
  of_native_maps core3300 DegreeTwoThreeSpectrum5587.graph DegreeTwoThreeSpectrum5588.graph
    sourceMap3300 fusedMap3300 sourceMap3300_checked fusedMap3300_checked
    DegreeTwoThreeFiniteComparisons.comparison3300
#print axioms sourceMap3300_checked
#print axioms fusedMap3300_checked
#print axioms certified3300
def sourceMap3300swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3300swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3300swap_checked : acceptsGraphIso
    (source (graph core3300) (root 9) 5 0) DegreeTwoThreeSpectrum5587.graph sourceMap3300swap=true := by decide +kernel
theorem fusedMap3300swap_checked : acceptsGraphIso
    (fused (graph core3300) (root 9) 5 0) DegreeTwoThreeSpectrum5588.graph fusedMap3300swap=true := by decide +kernel
theorem certified3300swap : Certified (graph core3300) (root 9) 5 0 :=
  of_native_maps core3300 DegreeTwoThreeSpectrum5587.graph DegreeTwoThreeSpectrum5588.graph
    sourceMap3300swap fusedMap3300swap sourceMap3300swap_checked fusedMap3300swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3300
#print axioms sourceMap3300swap_checked
#print axioms fusedMap3300swap_checked
#print axioms certified3300swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
