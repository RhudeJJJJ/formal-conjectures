/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1450 : Family 10 := level10.get ⟨109,by decide⟩
def sourceMap1450 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1450 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1450_checked : acceptsGraphIso
    (source (graph core1450) (root 10) 0 2) DegreeTwoThreeSpectrum2790.graph sourceMap1450=true := by decide +kernel
theorem fusedMap1450_checked : acceptsGraphIso
    (fused (graph core1450) (root 10) 0 2) DegreeTwoThreeSpectrum2369.graph fusedMap1450=true := by decide +kernel
theorem certified1450 : Certified (graph core1450) (root 10) 0 2 :=
  of_native_maps core1450 DegreeTwoThreeSpectrum2790.graph DegreeTwoThreeSpectrum2369.graph
    sourceMap1450 fusedMap1450 sourceMap1450_checked fusedMap1450_checked
    DegreeTwoThreeFiniteComparisons.comparison1450
#print axioms sourceMap1450_checked
#print axioms fusedMap1450_checked
#print axioms certified1450
def sourceMap1450swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1450swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1450swap_checked : acceptsGraphIso
    (source (graph core1450) (root 10) 2 0) DegreeTwoThreeSpectrum2790.graph sourceMap1450swap=true := by decide +kernel
theorem fusedMap1450swap_checked : acceptsGraphIso
    (fused (graph core1450) (root 10) 2 0) DegreeTwoThreeSpectrum2369.graph fusedMap1450swap=true := by decide +kernel
theorem certified1450swap : Certified (graph core1450) (root 10) 2 0 :=
  of_native_maps core1450 DegreeTwoThreeSpectrum2790.graph DegreeTwoThreeSpectrum2369.graph
    sourceMap1450swap fusedMap1450swap sourceMap1450swap_checked fusedMap1450swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1450
#print axioms sourceMap1450swap_checked
#print axioms fusedMap1450swap_checked
#print axioms certified1450swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
