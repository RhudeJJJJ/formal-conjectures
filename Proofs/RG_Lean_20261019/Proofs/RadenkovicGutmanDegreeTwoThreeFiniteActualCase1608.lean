/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1608 : Family 10 := level10.get ⟨630,by decide⟩
def sourceMap1608 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,13,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1608 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1608_checked : acceptsGraphIso
    (source (graph core1608) (root 10) 0 2) DegreeTwoThreeSpectrum3322.graph sourceMap1608=true := by decide +kernel
theorem fusedMap1608_checked : acceptsGraphIso
    (fused (graph core1608) (root 10) 0 2) DegreeTwoThreeSpectrum2574.graph fusedMap1608=true := by decide +kernel
theorem certified1608 : Certified (graph core1608) (root 10) 0 2 :=
  of_native_maps core1608 DegreeTwoThreeSpectrum3322.graph DegreeTwoThreeSpectrum2574.graph
    sourceMap1608 fusedMap1608 sourceMap1608_checked fusedMap1608_checked
    DegreeTwoThreeFiniteComparisons.comparison1608
#print axioms sourceMap1608_checked
#print axioms fusedMap1608_checked
#print axioms certified1608
def sourceMap1608swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,9,10,11,13] (sourceLabel 10 2 0 v)
def fusedMap1608swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1608swap_checked : acceptsGraphIso
    (source (graph core1608) (root 10) 2 0) DegreeTwoThreeSpectrum3322.graph sourceMap1608swap=true := by decide +kernel
theorem fusedMap1608swap_checked : acceptsGraphIso
    (fused (graph core1608) (root 10) 2 0) DegreeTwoThreeSpectrum2574.graph fusedMap1608swap=true := by decide +kernel
theorem certified1608swap : Certified (graph core1608) (root 10) 2 0 :=
  of_native_maps core1608 DegreeTwoThreeSpectrum3322.graph DegreeTwoThreeSpectrum2574.graph
    sourceMap1608swap fusedMap1608swap sourceMap1608swap_checked fusedMap1608swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1608
#print axioms sourceMap1608swap_checked
#print axioms fusedMap1608swap_checked
#print axioms certified1608swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
