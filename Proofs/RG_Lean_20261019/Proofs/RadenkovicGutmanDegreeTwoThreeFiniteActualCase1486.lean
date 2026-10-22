/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1486 : Family 10 := level10.get ⟨245,by decide⟩
def sourceMap1486 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1486 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1486_checked : acceptsGraphIso
    (source (graph core1486) (root 10) 0 2) DegreeTwoThreeSpectrum2576.graph sourceMap1486=true := by decide +kernel
theorem fusedMap1486_checked : acceptsGraphIso
    (fused (graph core1486) (root 10) 0 2) DegreeTwoThreeSpectrum2578.graph fusedMap1486=true := by decide +kernel
theorem certified1486 : Certified (graph core1486) (root 10) 0 2 :=
  of_native_maps core1486 DegreeTwoThreeSpectrum2576.graph DegreeTwoThreeSpectrum2578.graph
    sourceMap1486 fusedMap1486 sourceMap1486_checked fusedMap1486_checked
    DegreeTwoThreeFiniteComparisons.comparison1486
#print axioms sourceMap1486_checked
#print axioms fusedMap1486_checked
#print axioms certified1486
def sourceMap1486swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1486swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1486swap_checked : acceptsGraphIso
    (source (graph core1486) (root 10) 2 0) DegreeTwoThreeSpectrum2576.graph sourceMap1486swap=true := by decide +kernel
theorem fusedMap1486swap_checked : acceptsGraphIso
    (fused (graph core1486) (root 10) 2 0) DegreeTwoThreeSpectrum2578.graph fusedMap1486swap=true := by decide +kernel
theorem certified1486swap : Certified (graph core1486) (root 10) 2 0 :=
  of_native_maps core1486 DegreeTwoThreeSpectrum2576.graph DegreeTwoThreeSpectrum2578.graph
    sourceMap1486swap fusedMap1486swap sourceMap1486swap_checked fusedMap1486swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1486
#print axioms sourceMap1486swap_checked
#print axioms fusedMap1486swap_checked
#print axioms certified1486swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
