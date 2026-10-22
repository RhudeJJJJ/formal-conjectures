/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1508 : Family 10 := level10.get ⟨320,by decide⟩
def sourceMap1508 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,14,12,13,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1508 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,13,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1508_checked : acceptsGraphIso
    (source (graph core1508) (root 10) 0 2) DegreeTwoThreeSpectrum2724.graph sourceMap1508=true := by decide +kernel
theorem fusedMap1508_checked : acceptsGraphIso
    (fused (graph core1508) (root 10) 0 2) DegreeTwoThreeSpectrum2729.graph fusedMap1508=true := by decide +kernel
theorem certified1508 : Certified (graph core1508) (root 10) 0 2 :=
  of_native_maps core1508 DegreeTwoThreeSpectrum2724.graph DegreeTwoThreeSpectrum2729.graph
    sourceMap1508 fusedMap1508 sourceMap1508_checked fusedMap1508_checked
    DegreeTwoThreeFiniteComparisons.comparison1508
#print axioms sourceMap1508_checked
#print axioms fusedMap1508_checked
#print axioms certified1508
def sourceMap1508swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,14,12,9,10,11,13] (sourceLabel 10 2 0 v)
def fusedMap1508swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,13,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1508swap_checked : acceptsGraphIso
    (source (graph core1508) (root 10) 2 0) DegreeTwoThreeSpectrum2724.graph sourceMap1508swap=true := by decide +kernel
theorem fusedMap1508swap_checked : acceptsGraphIso
    (fused (graph core1508) (root 10) 2 0) DegreeTwoThreeSpectrum2729.graph fusedMap1508swap=true := by decide +kernel
theorem certified1508swap : Certified (graph core1508) (root 10) 2 0 :=
  of_native_maps core1508 DegreeTwoThreeSpectrum2724.graph DegreeTwoThreeSpectrum2729.graph
    sourceMap1508swap fusedMap1508swap sourceMap1508swap_checked fusedMap1508swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1508
#print axioms sourceMap1508swap_checked
#print axioms fusedMap1508swap_checked
#print axioms certified1508swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
