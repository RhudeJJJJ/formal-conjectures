/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1669 : Family 10 := level10.get ⟨797,by decide⟩
def sourceMap1669 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,14,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1669 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1669_checked : acceptsGraphIso
    (source (graph core1669) (root 10) 0 2) DegreeTwoThreeSpectrum3579.graph sourceMap1669=true := by decide +kernel
theorem fusedMap1669_checked : acceptsGraphIso
    (fused (graph core1669) (root 10) 0 2) DegreeTwoThreeSpectrum2767.graph fusedMap1669=true := by decide +kernel
theorem certified1669 : Certified (graph core1669) (root 10) 0 2 :=
  of_native_maps core1669 DegreeTwoThreeSpectrum3579.graph DegreeTwoThreeSpectrum2767.graph
    sourceMap1669 fusedMap1669 sourceMap1669_checked fusedMap1669_checked
    DegreeTwoThreeFiniteComparisons.comparison1669
#print axioms sourceMap1669_checked
#print axioms fusedMap1669_checked
#print axioms certified1669
def sourceMap1669swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10,14] (sourceLabel 10 2 0 v)
def fusedMap1669swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1669swap_checked : acceptsGraphIso
    (source (graph core1669) (root 10) 2 0) DegreeTwoThreeSpectrum3579.graph sourceMap1669swap=true := by decide +kernel
theorem fusedMap1669swap_checked : acceptsGraphIso
    (fused (graph core1669) (root 10) 2 0) DegreeTwoThreeSpectrum2767.graph fusedMap1669swap=true := by decide +kernel
theorem certified1669swap : Certified (graph core1669) (root 10) 2 0 :=
  of_native_maps core1669 DegreeTwoThreeSpectrum3579.graph DegreeTwoThreeSpectrum2767.graph
    sourceMap1669swap fusedMap1669swap sourceMap1669swap_checked fusedMap1669swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1669
#print axioms sourceMap1669swap_checked
#print axioms fusedMap1669swap_checked
#print axioms certified1669swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
