/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1599 : Family 10 := level10.get ⟨601,by decide⟩
def sourceMap1599 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1599 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1599_checked : acceptsGraphIso
    (source (graph core1599) (root 10) 0 2) DegreeTwoThreeSpectrum3261.graph sourceMap1599=true := by decide +kernel
theorem fusedMap1599_checked : acceptsGraphIso
    (fused (graph core1599) (root 10) 0 2) DegreeTwoThreeSpectrum2543.graph fusedMap1599=true := by decide +kernel
theorem certified1599 : Certified (graph core1599) (root 10) 0 2 :=
  of_native_maps core1599 DegreeTwoThreeSpectrum3261.graph DegreeTwoThreeSpectrum2543.graph
    sourceMap1599 fusedMap1599 sourceMap1599_checked fusedMap1599_checked
    DegreeTwoThreeFiniteComparisons.comparison1599
#print axioms sourceMap1599_checked
#print axioms fusedMap1599_checked
#print axioms certified1599
def sourceMap1599swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1599swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1599swap_checked : acceptsGraphIso
    (source (graph core1599) (root 10) 2 0) DegreeTwoThreeSpectrum3261.graph sourceMap1599swap=true := by decide +kernel
theorem fusedMap1599swap_checked : acceptsGraphIso
    (fused (graph core1599) (root 10) 2 0) DegreeTwoThreeSpectrum2543.graph fusedMap1599swap=true := by decide +kernel
theorem certified1599swap : Certified (graph core1599) (root 10) 2 0 :=
  of_native_maps core1599 DegreeTwoThreeSpectrum3261.graph DegreeTwoThreeSpectrum2543.graph
    sourceMap1599swap fusedMap1599swap sourceMap1599swap_checked fusedMap1599swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1599
#print axioms sourceMap1599swap_checked
#print axioms fusedMap1599swap_checked
#print axioms certified1599swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
