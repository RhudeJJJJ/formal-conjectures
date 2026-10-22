/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1613 : Family 10 := level10.get ⟨644,by decide⟩
def sourceMap1613 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,11,12,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1613 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1613_checked : acceptsGraphIso
    (source (graph core1613) (root 10) 0 2) DegreeTwoThreeSpectrum3342.graph sourceMap1613=true := by decide +kernel
theorem fusedMap1613_checked : acceptsGraphIso
    (fused (graph core1613) (root 10) 0 2) DegreeTwoThreeSpectrum2587.graph fusedMap1613=true := by decide +kernel
theorem certified1613 : Certified (graph core1613) (root 10) 0 2 :=
  of_native_maps core1613 DegreeTwoThreeSpectrum3342.graph DegreeTwoThreeSpectrum2587.graph
    sourceMap1613 fusedMap1613 sourceMap1613_checked fusedMap1613_checked
    DegreeTwoThreeFiniteComparisons.comparison1613
#print axioms sourceMap1613_checked
#print axioms fusedMap1613_checked
#print axioms certified1613
def sourceMap1613swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,11,8,9,10,12] (sourceLabel 10 2 0 v)
def fusedMap1613swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1613swap_checked : acceptsGraphIso
    (source (graph core1613) (root 10) 2 0) DegreeTwoThreeSpectrum3342.graph sourceMap1613swap=true := by decide +kernel
theorem fusedMap1613swap_checked : acceptsGraphIso
    (fused (graph core1613) (root 10) 2 0) DegreeTwoThreeSpectrum2587.graph fusedMap1613swap=true := by decide +kernel
theorem certified1613swap : Certified (graph core1613) (root 10) 2 0 :=
  of_native_maps core1613 DegreeTwoThreeSpectrum3342.graph DegreeTwoThreeSpectrum2587.graph
    sourceMap1613swap fusedMap1613swap sourceMap1613swap_checked fusedMap1613swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1613
#print axioms sourceMap1613swap_checked
#print axioms fusedMap1613swap_checked
#print axioms certified1613swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
