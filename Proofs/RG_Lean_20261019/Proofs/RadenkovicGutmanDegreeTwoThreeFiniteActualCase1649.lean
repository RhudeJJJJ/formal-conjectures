/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1649 : Family 10 := level10.get ⟨745,by decide⟩
def sourceMap1649 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1649 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1649_checked : acceptsGraphIso
    (source (graph core1649) (root 10) 0 2) DegreeTwoThreeSpectrum3507.graph sourceMap1649=true := by decide +kernel
theorem fusedMap1649_checked : acceptsGraphIso
    (fused (graph core1649) (root 10) 0 2) DegreeTwoThreeSpectrum2707.graph fusedMap1649=true := by decide +kernel
theorem certified1649 : Certified (graph core1649) (root 10) 0 2 :=
  of_native_maps core1649 DegreeTwoThreeSpectrum3507.graph DegreeTwoThreeSpectrum2707.graph
    sourceMap1649 fusedMap1649 sourceMap1649_checked fusedMap1649_checked
    DegreeTwoThreeFiniteComparisons.comparison1649
#print axioms sourceMap1649_checked
#print axioms fusedMap1649_checked
#print axioms certified1649
def sourceMap1649swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1649swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1649swap_checked : acceptsGraphIso
    (source (graph core1649) (root 10) 2 0) DegreeTwoThreeSpectrum3507.graph sourceMap1649swap=true := by decide +kernel
theorem fusedMap1649swap_checked : acceptsGraphIso
    (fused (graph core1649) (root 10) 2 0) DegreeTwoThreeSpectrum2707.graph fusedMap1649swap=true := by decide +kernel
theorem certified1649swap : Certified (graph core1649) (root 10) 2 0 :=
  of_native_maps core1649 DegreeTwoThreeSpectrum3507.graph DegreeTwoThreeSpectrum2707.graph
    sourceMap1649swap fusedMap1649swap sourceMap1649swap_checked fusedMap1649swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1649
#print axioms sourceMap1649swap_checked
#print axioms fusedMap1649swap_checked
#print axioms certified1649swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
