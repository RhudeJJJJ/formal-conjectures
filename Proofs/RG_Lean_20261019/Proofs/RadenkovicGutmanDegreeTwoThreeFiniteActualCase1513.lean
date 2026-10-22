/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1513 : Family 10 := level10.get ⟨339,by decide⟩
def sourceMap1513 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,14,12,13,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1513 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,13,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1513_checked : acceptsGraphIso
    (source (graph core1513) (root 10) 0 2) DegreeTwoThreeSpectrum2764.graph sourceMap1513=true := by decide +kernel
theorem fusedMap1513_checked : acceptsGraphIso
    (fused (graph core1513) (root 10) 0 2) DegreeTwoThreeSpectrum2769.graph fusedMap1513=true := by decide +kernel
theorem certified1513 : Certified (graph core1513) (root 10) 0 2 :=
  of_native_maps core1513 DegreeTwoThreeSpectrum2764.graph DegreeTwoThreeSpectrum2769.graph
    sourceMap1513 fusedMap1513 sourceMap1513_checked fusedMap1513_checked
    DegreeTwoThreeFiniteComparisons.comparison1513
#print axioms sourceMap1513_checked
#print axioms fusedMap1513_checked
#print axioms certified1513
def sourceMap1513swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,14,12,9,10,11,13] (sourceLabel 10 2 0 v)
def fusedMap1513swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,13,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1513swap_checked : acceptsGraphIso
    (source (graph core1513) (root 10) 2 0) DegreeTwoThreeSpectrum2764.graph sourceMap1513swap=true := by decide +kernel
theorem fusedMap1513swap_checked : acceptsGraphIso
    (fused (graph core1513) (root 10) 2 0) DegreeTwoThreeSpectrum2769.graph fusedMap1513swap=true := by decide +kernel
theorem certified1513swap : Certified (graph core1513) (root 10) 2 0 :=
  of_native_maps core1513 DegreeTwoThreeSpectrum2764.graph DegreeTwoThreeSpectrum2769.graph
    sourceMap1513swap fusedMap1513swap sourceMap1513swap_checked fusedMap1513swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1513
#print axioms sourceMap1513swap_checked
#print axioms fusedMap1513swap_checked
#print axioms certified1513swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
