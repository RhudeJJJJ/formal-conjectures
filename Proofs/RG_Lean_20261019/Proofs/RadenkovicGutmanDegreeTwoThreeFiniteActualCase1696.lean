/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1696 : Family 10 := level10.get ⟨871,by decide⟩
def sourceMap1696 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,2,3,4,8,5,6,7] (sourceLabel 10 0 2 v)
def fusedMap1696 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1696_checked : acceptsGraphIso
    (source (graph core1696) (root 10) 0 2) DegreeTwoThreeSpectrum3624.graph sourceMap1696=true := by decide +kernel
theorem fusedMap1696_checked : acceptsGraphIso
    (fused (graph core1696) (root 10) 0 2) DegreeTwoThreeSpectrum2867.graph fusedMap1696=true := by decide +kernel
theorem certified1696 : Certified (graph core1696) (root 10) 0 2 :=
  of_native_maps core1696 DegreeTwoThreeSpectrum3624.graph DegreeTwoThreeSpectrum2867.graph
    sourceMap1696 fusedMap1696 sourceMap1696_checked fusedMap1696_checked
    DegreeTwoThreeFiniteComparisons.comparison1696
#print axioms sourceMap1696_checked
#print axioms fusedMap1696_checked
#print axioms certified1696
def sourceMap1696swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,2,3,4,5,6,7,8] (sourceLabel 10 2 0 v)
def fusedMap1696swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1696swap_checked : acceptsGraphIso
    (source (graph core1696) (root 10) 2 0) DegreeTwoThreeSpectrum3624.graph sourceMap1696swap=true := by decide +kernel
theorem fusedMap1696swap_checked : acceptsGraphIso
    (fused (graph core1696) (root 10) 2 0) DegreeTwoThreeSpectrum2867.graph fusedMap1696swap=true := by decide +kernel
theorem certified1696swap : Certified (graph core1696) (root 10) 2 0 :=
  of_native_maps core1696 DegreeTwoThreeSpectrum3624.graph DegreeTwoThreeSpectrum2867.graph
    sourceMap1696swap fusedMap1696swap sourceMap1696swap_checked fusedMap1696swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1696
#print axioms sourceMap1696swap_checked
#print axioms fusedMap1696swap_checked
#print axioms certified1696swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
