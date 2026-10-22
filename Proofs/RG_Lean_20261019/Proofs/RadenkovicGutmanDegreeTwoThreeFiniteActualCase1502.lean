/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1502 : Family 10 := level10.get ⟨298,by decide⟩
def sourceMap1502 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1502 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1502_checked : acceptsGraphIso
    (source (graph core1502) (root 10) 0 2) DegreeTwoThreeSpectrum2679.graph sourceMap1502=true := by decide +kernel
theorem fusedMap1502_checked : acceptsGraphIso
    (fused (graph core1502) (root 10) 0 2) DegreeTwoThreeSpectrum2681.graph fusedMap1502=true := by decide +kernel
theorem certified1502 : Certified (graph core1502) (root 10) 0 2 :=
  of_native_maps core1502 DegreeTwoThreeSpectrum2679.graph DegreeTwoThreeSpectrum2681.graph
    sourceMap1502 fusedMap1502 sourceMap1502_checked fusedMap1502_checked
    DegreeTwoThreeFiniteComparisons.comparison1502
#print axioms sourceMap1502_checked
#print axioms fusedMap1502_checked
#print axioms certified1502
def sourceMap1502swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1502swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1502swap_checked : acceptsGraphIso
    (source (graph core1502) (root 10) 2 0) DegreeTwoThreeSpectrum2679.graph sourceMap1502swap=true := by decide +kernel
theorem fusedMap1502swap_checked : acceptsGraphIso
    (fused (graph core1502) (root 10) 2 0) DegreeTwoThreeSpectrum2681.graph fusedMap1502swap=true := by decide +kernel
theorem certified1502swap : Certified (graph core1502) (root 10) 2 0 :=
  of_native_maps core1502 DegreeTwoThreeSpectrum2679.graph DegreeTwoThreeSpectrum2681.graph
    sourceMap1502swap fusedMap1502swap sourceMap1502swap_checked fusedMap1502swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1502
#print axioms sourceMap1502swap_checked
#print axioms fusedMap1502swap_checked
#print axioms certified1502swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
