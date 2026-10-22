/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1464 : Family 10 := level10.get ⟨162,by decide⟩
def sourceMap1464 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,1,0,9,10,11,12,13,14,6,7,8,3,4,5] (sourceLabel 10 0 2 v)
def fusedMap1464 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,6,7,2,3,4,5] (fusedLabel 10 0 2 v)
theorem sourceMap1464_checked : acceptsGraphIso
    (source (graph core1464) (root 10) 0 2) DegreeTwoThreeSpectrum2855.graph sourceMap1464=true := by decide +kernel
theorem fusedMap1464_checked : acceptsGraphIso
    (fused (graph core1464) (root 10) 0 2) DegreeTwoThreeSpectrum2412.graph fusedMap1464=true := by decide +kernel
theorem certified1464 : Certified (graph core1464) (root 10) 0 2 :=
  of_native_maps core1464 DegreeTwoThreeSpectrum2855.graph DegreeTwoThreeSpectrum2412.graph
    sourceMap1464 fusedMap1464 sourceMap1464_checked fusedMap1464_checked
    DegreeTwoThreeFiniteComparisons.comparison1464
#print axioms sourceMap1464_checked
#print axioms fusedMap1464_checked
#print axioms certified1464
def sourceMap1464swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,1,0,9,10,11,12,13,14,6,7,3,4,5,8] (sourceLabel 10 2 0 v)
def fusedMap1464swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,6,7,2,3,4,5] (fusedLabel 10 2 0 v)
theorem sourceMap1464swap_checked : acceptsGraphIso
    (source (graph core1464) (root 10) 2 0) DegreeTwoThreeSpectrum2855.graph sourceMap1464swap=true := by decide +kernel
theorem fusedMap1464swap_checked : acceptsGraphIso
    (fused (graph core1464) (root 10) 2 0) DegreeTwoThreeSpectrum2412.graph fusedMap1464swap=true := by decide +kernel
theorem certified1464swap : Certified (graph core1464) (root 10) 2 0 :=
  of_native_maps core1464 DegreeTwoThreeSpectrum2855.graph DegreeTwoThreeSpectrum2412.graph
    sourceMap1464swap fusedMap1464swap sourceMap1464swap_checked fusedMap1464swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1464
#print axioms sourceMap1464swap_checked
#print axioms fusedMap1464swap_checked
#print axioms certified1464swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
