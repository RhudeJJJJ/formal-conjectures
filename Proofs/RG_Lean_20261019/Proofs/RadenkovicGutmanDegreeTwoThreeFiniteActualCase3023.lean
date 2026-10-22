/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3023 : Family 10 := level10.get ⟨1622,by decide⟩
def sourceMap3023 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3023 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3023_checked : acceptsGraphIso
    (source (graph core3023) (root 10) 0 4) DegreeTwoThreeSpectrum7179.graph sourceMap3023=true := by decide +kernel
theorem fusedMap3023_checked : acceptsGraphIso
    (fused (graph core3023) (root 10) 0 4) DegreeTwoThreeSpectrum6180.graph fusedMap3023=true := by decide +kernel
theorem certified3023 : Certified (graph core3023) (root 10) 0 4 :=
  of_native_maps core3023 DegreeTwoThreeSpectrum7179.graph DegreeTwoThreeSpectrum6180.graph
    sourceMap3023 fusedMap3023 sourceMap3023_checked fusedMap3023_checked
    DegreeTwoThreeFiniteComparisons.comparison3023
#print axioms sourceMap3023_checked
#print axioms fusedMap3023_checked
#print axioms certified3023
def sourceMap3023swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3023swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3023swap_checked : acceptsGraphIso
    (source (graph core3023) (root 10) 4 0) DegreeTwoThreeSpectrum7179.graph sourceMap3023swap=true := by decide +kernel
theorem fusedMap3023swap_checked : acceptsGraphIso
    (fused (graph core3023) (root 10) 4 0) DegreeTwoThreeSpectrum6180.graph fusedMap3023swap=true := by decide +kernel
theorem certified3023swap : Certified (graph core3023) (root 10) 4 0 :=
  of_native_maps core3023 DegreeTwoThreeSpectrum7179.graph DegreeTwoThreeSpectrum6180.graph
    sourceMap3023swap fusedMap3023swap sourceMap3023swap_checked fusedMap3023swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3023
#print axioms sourceMap3023swap_checked
#print axioms fusedMap3023swap_checked
#print axioms certified3023swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
