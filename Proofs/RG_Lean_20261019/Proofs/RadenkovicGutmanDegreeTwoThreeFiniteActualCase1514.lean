/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1514 : Family 10 := level10.get ⟨340,by decide⟩
def sourceMap1514 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1514 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1514_checked : acceptsGraphIso
    (source (graph core1514) (root 10) 0 2) DegreeTwoThreeSpectrum2763.graph sourceMap1514=true := by decide +kernel
theorem fusedMap1514_checked : acceptsGraphIso
    (fused (graph core1514) (root 10) 0 2) DegreeTwoThreeSpectrum2768.graph fusedMap1514=true := by decide +kernel
theorem certified1514 : Certified (graph core1514) (root 10) 0 2 :=
  of_native_maps core1514 DegreeTwoThreeSpectrum2763.graph DegreeTwoThreeSpectrum2768.graph
    sourceMap1514 fusedMap1514 sourceMap1514_checked fusedMap1514_checked
    DegreeTwoThreeFiniteComparisons.comparison1514
#print axioms sourceMap1514_checked
#print axioms fusedMap1514_checked
#print axioms certified1514
def sourceMap1514swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1514swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1514swap_checked : acceptsGraphIso
    (source (graph core1514) (root 10) 2 0) DegreeTwoThreeSpectrum2763.graph sourceMap1514swap=true := by decide +kernel
theorem fusedMap1514swap_checked : acceptsGraphIso
    (fused (graph core1514) (root 10) 2 0) DegreeTwoThreeSpectrum2768.graph fusedMap1514swap=true := by decide +kernel
theorem certified1514swap : Certified (graph core1514) (root 10) 2 0 :=
  of_native_maps core1514 DegreeTwoThreeSpectrum2763.graph DegreeTwoThreeSpectrum2768.graph
    sourceMap1514swap fusedMap1514swap sourceMap1514swap_checked fusedMap1514swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1514
#print axioms sourceMap1514swap_checked
#print axioms fusedMap1514swap_checked
#print axioms certified1514swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
