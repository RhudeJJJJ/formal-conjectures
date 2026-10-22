/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1517 : Family 10 := level10.get ⟨352,by decide⟩
def sourceMap1517 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,14,12,13,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1517 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,13,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1517_checked : acceptsGraphIso
    (source (graph core1517) (root 10) 0 2) DegreeTwoThreeSpectrum2789.graph sourceMap1517=true := by decide +kernel
theorem fusedMap1517_checked : acceptsGraphIso
    (fused (graph core1517) (root 10) 0 2) DegreeTwoThreeSpectrum2794.graph fusedMap1517=true := by decide +kernel
theorem certified1517 : Certified (graph core1517) (root 10) 0 2 :=
  of_native_maps core1517 DegreeTwoThreeSpectrum2789.graph DegreeTwoThreeSpectrum2794.graph
    sourceMap1517 fusedMap1517 sourceMap1517_checked fusedMap1517_checked
    DegreeTwoThreeFiniteComparisons.comparison1517
#print axioms sourceMap1517_checked
#print axioms fusedMap1517_checked
#print axioms certified1517
def sourceMap1517swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,14,12,9,10,11,13] (sourceLabel 10 2 0 v)
def fusedMap1517swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,13,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1517swap_checked : acceptsGraphIso
    (source (graph core1517) (root 10) 2 0) DegreeTwoThreeSpectrum2789.graph sourceMap1517swap=true := by decide +kernel
theorem fusedMap1517swap_checked : acceptsGraphIso
    (fused (graph core1517) (root 10) 2 0) DegreeTwoThreeSpectrum2794.graph fusedMap1517swap=true := by decide +kernel
theorem certified1517swap : Certified (graph core1517) (root 10) 2 0 :=
  of_native_maps core1517 DegreeTwoThreeSpectrum2789.graph DegreeTwoThreeSpectrum2794.graph
    sourceMap1517swap fusedMap1517swap sourceMap1517swap_checked fusedMap1517swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1517
#print axioms sourceMap1517swap_checked
#print axioms fusedMap1517swap_checked
#print axioms certified1517swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
