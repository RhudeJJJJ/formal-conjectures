/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1697 : Family 10 := level10.get ⟨872,by decide⟩
def sourceMap1697 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,5,6,7,8,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1697 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1697_checked : acceptsGraphIso
    (source (graph core1697) (root 10) 0 2) DegreeTwoThreeSpectrum3656.graph sourceMap1697=true := by decide +kernel
theorem fusedMap1697_checked : acceptsGraphIso
    (fused (graph core1697) (root 10) 0 2) DegreeTwoThreeSpectrum2868.graph fusedMap1697=true := by decide +kernel
theorem certified1697 : Certified (graph core1697) (root 10) 0 2 :=
  of_native_maps core1697 DegreeTwoThreeSpectrum3656.graph DegreeTwoThreeSpectrum2868.graph
    sourceMap1697 fusedMap1697 sourceMap1697_checked fusedMap1697_checked
    DegreeTwoThreeFiniteComparisons.comparison1697
#print axioms sourceMap1697_checked
#print axioms fusedMap1697_checked
#print axioms certified1697
def sourceMap1697swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,5,6,7,2,3,4,8] (sourceLabel 10 2 0 v)
def fusedMap1697swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1697swap_checked : acceptsGraphIso
    (source (graph core1697) (root 10) 2 0) DegreeTwoThreeSpectrum3656.graph sourceMap1697swap=true := by decide +kernel
theorem fusedMap1697swap_checked : acceptsGraphIso
    (fused (graph core1697) (root 10) 2 0) DegreeTwoThreeSpectrum2868.graph fusedMap1697swap=true := by decide +kernel
theorem certified1697swap : Certified (graph core1697) (root 10) 2 0 :=
  of_native_maps core1697 DegreeTwoThreeSpectrum3656.graph DegreeTwoThreeSpectrum2868.graph
    sourceMap1697swap fusedMap1697swap sourceMap1697swap_checked fusedMap1697swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1697
#print axioms sourceMap1697swap_checked
#print axioms fusedMap1697swap_checked
#print axioms certified1697swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
