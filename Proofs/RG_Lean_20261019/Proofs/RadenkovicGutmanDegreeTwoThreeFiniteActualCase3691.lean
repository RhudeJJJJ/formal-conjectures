/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3691 : Family 7 := level7.get ⟨87,by decide⟩
def sourceMap3691 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3691 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3691_checked : acceptsGraphIso
    (source (graph core3691) (root 7) 0 7) DegreeTwoThreeSpectrum5486.graph sourceMap3691=true := by decide +kernel
theorem fusedMap3691_checked : acceptsGraphIso
    (fused (graph core3691) (root 7) 0 7) DegreeTwoThreeSpectrum5489.graph fusedMap3691=true := by decide +kernel
theorem certified3691 : Certified (graph core3691) (root 7) 0 7 :=
  of_native_maps core3691 DegreeTwoThreeSpectrum5486.graph DegreeTwoThreeSpectrum5489.graph
    sourceMap3691 fusedMap3691 sourceMap3691_checked fusedMap3691_checked
    DegreeTwoThreeFiniteComparisons.comparison3691
#print axioms sourceMap3691_checked
#print axioms fusedMap3691_checked
#print axioms certified3691
def sourceMap3691swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,16,10] (sourceLabel 7 7 0 v)
def fusedMap3691swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3691swap_checked : acceptsGraphIso
    (source (graph core3691) (root 7) 7 0) DegreeTwoThreeSpectrum5486.graph sourceMap3691swap=true := by decide +kernel
theorem fusedMap3691swap_checked : acceptsGraphIso
    (fused (graph core3691) (root 7) 7 0) DegreeTwoThreeSpectrum5489.graph fusedMap3691swap=true := by decide +kernel
theorem certified3691swap : Certified (graph core3691) (root 7) 7 0 :=
  of_native_maps core3691 DegreeTwoThreeSpectrum5486.graph DegreeTwoThreeSpectrum5489.graph
    sourceMap3691swap fusedMap3691swap sourceMap3691swap_checked fusedMap3691swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3691
#print axioms sourceMap3691swap_checked
#print axioms fusedMap3691swap_checked
#print axioms certified3691swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
