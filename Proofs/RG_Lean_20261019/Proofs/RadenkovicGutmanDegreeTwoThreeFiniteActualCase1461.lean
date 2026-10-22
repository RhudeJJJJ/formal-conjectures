/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1461 : Family 10 := level10.get ⟨154,by decide⟩
def sourceMap1461 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,1,0,8,9,10,11,12,13,14,6,7,3,4,5] (sourceLabel 10 0 2 v)
def fusedMap1461 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1461_checked : acceptsGraphIso
    (source (graph core1461) (root 10) 0 2) DegreeTwoThreeSpectrum2906.graph sourceMap1461=true := by decide +kernel
theorem fusedMap1461_checked : acceptsGraphIso
    (fused (graph core1461) (root 10) 0 2) DegreeTwoThreeSpectrum2416.graph fusedMap1461=true := by decide +kernel
theorem certified1461 : Certified (graph core1461) (root 10) 0 2 :=
  of_native_maps core1461 DegreeTwoThreeSpectrum2906.graph DegreeTwoThreeSpectrum2416.graph
    sourceMap1461 fusedMap1461 sourceMap1461_checked fusedMap1461_checked
    DegreeTwoThreeFiniteComparisons.comparison1461
#print axioms sourceMap1461_checked
#print axioms fusedMap1461_checked
#print axioms certified1461
def sourceMap1461swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,1,0,8,9,10,11,12,13,14,6,3,4,5,7] (sourceLabel 10 2 0 v)
def fusedMap1461swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1461swap_checked : acceptsGraphIso
    (source (graph core1461) (root 10) 2 0) DegreeTwoThreeSpectrum2906.graph sourceMap1461swap=true := by decide +kernel
theorem fusedMap1461swap_checked : acceptsGraphIso
    (fused (graph core1461) (root 10) 2 0) DegreeTwoThreeSpectrum2416.graph fusedMap1461swap=true := by decide +kernel
theorem certified1461swap : Certified (graph core1461) (root 10) 2 0 :=
  of_native_maps core1461 DegreeTwoThreeSpectrum2906.graph DegreeTwoThreeSpectrum2416.graph
    sourceMap1461swap fusedMap1461swap sourceMap1461swap_checked fusedMap1461swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1461
#print axioms sourceMap1461swap_checked
#print axioms fusedMap1461swap_checked
#print axioms certified1461swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
