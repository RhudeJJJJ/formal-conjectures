/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1632 : Family 10 := level10.get ⟨694,by decide⟩
def sourceMap1632 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1632 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1632_checked : acceptsGraphIso
    (source (graph core1632) (root 10) 0 2) DegreeTwoThreeSpectrum3410.graph sourceMap1632=true := by decide +kernel
theorem fusedMap1632_checked : acceptsGraphIso
    (fused (graph core1632) (root 10) 0 2) DegreeTwoThreeSpectrum2653.graph fusedMap1632=true := by decide +kernel
theorem certified1632 : Certified (graph core1632) (root 10) 0 2 :=
  of_native_maps core1632 DegreeTwoThreeSpectrum3410.graph DegreeTwoThreeSpectrum2653.graph
    sourceMap1632 fusedMap1632 sourceMap1632_checked fusedMap1632_checked
    DegreeTwoThreeFiniteComparisons.comparison1632
#print axioms sourceMap1632_checked
#print axioms fusedMap1632_checked
#print axioms certified1632
def sourceMap1632swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1632swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1632swap_checked : acceptsGraphIso
    (source (graph core1632) (root 10) 2 0) DegreeTwoThreeSpectrum3410.graph sourceMap1632swap=true := by decide +kernel
theorem fusedMap1632swap_checked : acceptsGraphIso
    (fused (graph core1632) (root 10) 2 0) DegreeTwoThreeSpectrum2653.graph fusedMap1632swap=true := by decide +kernel
theorem certified1632swap : Certified (graph core1632) (root 10) 2 0 :=
  of_native_maps core1632 DegreeTwoThreeSpectrum3410.graph DegreeTwoThreeSpectrum2653.graph
    sourceMap1632swap fusedMap1632swap sourceMap1632swap_checked fusedMap1632swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1632
#print axioms sourceMap1632swap_checked
#print axioms fusedMap1632swap_checked
#print axioms certified1632swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
