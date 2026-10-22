/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1633 : Family 10 := level10.get ⟨697,by decide⟩
def sourceMap1633 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,13,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1633 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1633_checked : acceptsGraphIso
    (source (graph core1633) (root 10) 0 2) DegreeTwoThreeSpectrum3415.graph sourceMap1633=true := by decide +kernel
theorem fusedMap1633_checked : acceptsGraphIso
    (fused (graph core1633) (root 10) 0 2) DegreeTwoThreeSpectrum2656.graph fusedMap1633=true := by decide +kernel
theorem certified1633 : Certified (graph core1633) (root 10) 0 2 :=
  of_native_maps core1633 DegreeTwoThreeSpectrum3415.graph DegreeTwoThreeSpectrum2656.graph
    sourceMap1633 fusedMap1633 sourceMap1633_checked fusedMap1633_checked
    DegreeTwoThreeFiniteComparisons.comparison1633
#print axioms sourceMap1633_checked
#print axioms fusedMap1633_checked
#print axioms certified1633
def sourceMap1633swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,9,10,11,13] (sourceLabel 10 2 0 v)
def fusedMap1633swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1633swap_checked : acceptsGraphIso
    (source (graph core1633) (root 10) 2 0) DegreeTwoThreeSpectrum3415.graph sourceMap1633swap=true := by decide +kernel
theorem fusedMap1633swap_checked : acceptsGraphIso
    (fused (graph core1633) (root 10) 2 0) DegreeTwoThreeSpectrum2656.graph fusedMap1633swap=true := by decide +kernel
theorem certified1633swap : Certified (graph core1633) (root 10) 2 0 :=
  of_native_maps core1633 DegreeTwoThreeSpectrum3415.graph DegreeTwoThreeSpectrum2656.graph
    sourceMap1633swap fusedMap1633swap sourceMap1633swap_checked fusedMap1633swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1633
#print axioms sourceMap1633swap_checked
#print axioms fusedMap1633swap_checked
#print axioms certified1633swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
