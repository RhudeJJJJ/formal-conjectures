/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1641 : Family 10 := level10.get ⟨719,by decide⟩
def sourceMap1641 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,11,12,13,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1641 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1641_checked : acceptsGraphIso
    (source (graph core1641) (root 10) 0 2) DegreeTwoThreeSpectrum3451.graph sourceMap1641=true := by decide +kernel
theorem fusedMap1641_checked : acceptsGraphIso
    (fused (graph core1641) (root 10) 0 2) DegreeTwoThreeSpectrum2680.graph fusedMap1641=true := by decide +kernel
theorem certified1641 : Certified (graph core1641) (root 10) 0 2 :=
  of_native_maps core1641 DegreeTwoThreeSpectrum3451.graph DegreeTwoThreeSpectrum2680.graph
    sourceMap1641 fusedMap1641 sourceMap1641_checked fusedMap1641_checked
    DegreeTwoThreeFiniteComparisons.comparison1641
#print axioms sourceMap1641_checked
#print axioms fusedMap1641_checked
#print axioms certified1641
def sourceMap1641swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,11,12,8,9,10,13] (sourceLabel 10 2 0 v)
def fusedMap1641swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1641swap_checked : acceptsGraphIso
    (source (graph core1641) (root 10) 2 0) DegreeTwoThreeSpectrum3451.graph sourceMap1641swap=true := by decide +kernel
theorem fusedMap1641swap_checked : acceptsGraphIso
    (fused (graph core1641) (root 10) 2 0) DegreeTwoThreeSpectrum2680.graph fusedMap1641swap=true := by decide +kernel
theorem certified1641swap : Certified (graph core1641) (root 10) 2 0 :=
  of_native_maps core1641 DegreeTwoThreeSpectrum3451.graph DegreeTwoThreeSpectrum2680.graph
    sourceMap1641swap fusedMap1641swap sourceMap1641swap_checked fusedMap1641swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1641
#print axioms sourceMap1641swap_checked
#print axioms fusedMap1641swap_checked
#print axioms certified1641swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
