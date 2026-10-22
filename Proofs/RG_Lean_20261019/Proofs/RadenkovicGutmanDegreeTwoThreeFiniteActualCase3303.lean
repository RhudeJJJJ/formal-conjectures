/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3303 : Family 9 := level9.get ⟨245,by decide⟩
def sourceMap3303 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3303 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3303_checked : acceptsGraphIso
    (source (graph core3303) (root 9) 0 5) DegreeTwoThreeSpectrum5621.graph sourceMap3303=true := by decide +kernel
theorem fusedMap3303_checked : acceptsGraphIso
    (fused (graph core3303) (root 9) 0 5) DegreeTwoThreeSpectrum5622.graph fusedMap3303=true := by decide +kernel
theorem certified3303 : Certified (graph core3303) (root 9) 0 5 :=
  of_native_maps core3303 DegreeTwoThreeSpectrum5621.graph DegreeTwoThreeSpectrum5622.graph
    sourceMap3303 fusedMap3303 sourceMap3303_checked fusedMap3303_checked
    DegreeTwoThreeFiniteComparisons.comparison3303
#print axioms sourceMap3303_checked
#print axioms fusedMap3303_checked
#print axioms certified3303
def sourceMap3303swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3303swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3303swap_checked : acceptsGraphIso
    (source (graph core3303) (root 9) 5 0) DegreeTwoThreeSpectrum5621.graph sourceMap3303swap=true := by decide +kernel
theorem fusedMap3303swap_checked : acceptsGraphIso
    (fused (graph core3303) (root 9) 5 0) DegreeTwoThreeSpectrum5622.graph fusedMap3303swap=true := by decide +kernel
theorem certified3303swap : Certified (graph core3303) (root 9) 5 0 :=
  of_native_maps core3303 DegreeTwoThreeSpectrum5621.graph DegreeTwoThreeSpectrum5622.graph
    sourceMap3303swap fusedMap3303swap sourceMap3303swap_checked fusedMap3303swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3303
#print axioms sourceMap3303swap_checked
#print axioms fusedMap3303swap_checked
#print axioms certified3303swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
