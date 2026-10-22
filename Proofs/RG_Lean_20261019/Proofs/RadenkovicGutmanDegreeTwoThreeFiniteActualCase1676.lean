/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1676 : Family 10 := level10.get ⟨817,by decide⟩
def sourceMap1676 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,14,7,8,9,13,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1676 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1676_checked : acceptsGraphIso
    (source (graph core1676) (root 10) 0 2) DegreeTwoThreeSpectrum3593.graph sourceMap1676=true := by decide +kernel
theorem fusedMap1676_checked : acceptsGraphIso
    (fused (graph core1676) (root 10) 0 2) DegreeTwoThreeSpectrum2791.graph fusedMap1676=true := by decide +kernel
theorem certified1676 : Certified (graph core1676) (root 10) 0 2 :=
  of_native_maps core1676 DegreeTwoThreeSpectrum3593.graph DegreeTwoThreeSpectrum2791.graph
    sourceMap1676 fusedMap1676 sourceMap1676_checked fusedMap1676_checked
    DegreeTwoThreeFiniteComparisons.comparison1676
#print axioms sourceMap1676_checked
#print axioms fusedMap1676_checked
#print axioms certified1676
def sourceMap1676swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,14,7,8,9,10,11,12,13] (sourceLabel 10 2 0 v)
def fusedMap1676swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1676swap_checked : acceptsGraphIso
    (source (graph core1676) (root 10) 2 0) DegreeTwoThreeSpectrum3593.graph sourceMap1676swap=true := by decide +kernel
theorem fusedMap1676swap_checked : acceptsGraphIso
    (fused (graph core1676) (root 10) 2 0) DegreeTwoThreeSpectrum2791.graph fusedMap1676swap=true := by decide +kernel
theorem certified1676swap : Certified (graph core1676) (root 10) 2 0 :=
  of_native_maps core1676 DegreeTwoThreeSpectrum3593.graph DegreeTwoThreeSpectrum2791.graph
    sourceMap1676swap fusedMap1676swap sourceMap1676swap_checked fusedMap1676swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1676
#print axioms sourceMap1676swap_checked
#print axioms fusedMap1676swap_checked
#print axioms certified1676swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
