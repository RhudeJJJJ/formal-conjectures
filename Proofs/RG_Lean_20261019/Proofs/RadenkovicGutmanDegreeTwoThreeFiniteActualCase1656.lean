/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1656 : Family 10 := level10.get ⟨760,by decide⟩
def sourceMap1656 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,14,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1656 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1656_checked : acceptsGraphIso
    (source (graph core1656) (root 10) 0 2) DegreeTwoThreeSpectrum3519.graph sourceMap1656=true := by decide +kernel
theorem fusedMap1656_checked : acceptsGraphIso
    (fused (graph core1656) (root 10) 0 2) DegreeTwoThreeSpectrum2727.graph fusedMap1656=true := by decide +kernel
theorem certified1656 : Certified (graph core1656) (root 10) 0 2 :=
  of_native_maps core1656 DegreeTwoThreeSpectrum3519.graph DegreeTwoThreeSpectrum2727.graph
    sourceMap1656 fusedMap1656 sourceMap1656_checked fusedMap1656_checked
    DegreeTwoThreeFiniteComparisons.comparison1656
#print axioms sourceMap1656_checked
#print axioms fusedMap1656_checked
#print axioms certified1656
def sourceMap1656swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10,14] (sourceLabel 10 2 0 v)
def fusedMap1656swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1656swap_checked : acceptsGraphIso
    (source (graph core1656) (root 10) 2 0) DegreeTwoThreeSpectrum3519.graph sourceMap1656swap=true := by decide +kernel
theorem fusedMap1656swap_checked : acceptsGraphIso
    (fused (graph core1656) (root 10) 2 0) DegreeTwoThreeSpectrum2727.graph fusedMap1656swap=true := by decide +kernel
theorem certified1656swap : Certified (graph core1656) (root 10) 2 0 :=
  of_native_maps core1656 DegreeTwoThreeSpectrum3519.graph DegreeTwoThreeSpectrum2727.graph
    sourceMap1656swap fusedMap1656swap sourceMap1656swap_checked fusedMap1656swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1656
#print axioms sourceMap1656swap_checked
#print axioms fusedMap1656swap_checked
#print axioms certified1656swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
