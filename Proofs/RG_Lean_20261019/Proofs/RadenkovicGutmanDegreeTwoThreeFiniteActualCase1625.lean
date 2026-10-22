/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1625 : Family 10 := level10.get ⟨671,by decide⟩
def sourceMap1625 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,14,10,11,12,13,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1625 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1625_checked : acceptsGraphIso
    (source (graph core1625) (root 10) 0 2) DegreeTwoThreeSpectrum3362.graph sourceMap1625=true := by decide +kernel
theorem fusedMap1625_checked : acceptsGraphIso
    (fused (graph core1625) (root 10) 0 2) DegreeTwoThreeSpectrum2623.graph fusedMap1625=true := by decide +kernel
theorem certified1625 : Certified (graph core1625) (root 10) 0 2 :=
  of_native_maps core1625 DegreeTwoThreeSpectrum3362.graph DegreeTwoThreeSpectrum2623.graph
    sourceMap1625 fusedMap1625 sourceMap1625_checked fusedMap1625_checked
    DegreeTwoThreeFiniteComparisons.comparison1625
#print axioms sourceMap1625_checked
#print axioms fusedMap1625_checked
#print axioms certified1625
def sourceMap1625swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,14,10,11,12,7,8,9,13] (sourceLabel 10 2 0 v)
def fusedMap1625swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1625swap_checked : acceptsGraphIso
    (source (graph core1625) (root 10) 2 0) DegreeTwoThreeSpectrum3362.graph sourceMap1625swap=true := by decide +kernel
theorem fusedMap1625swap_checked : acceptsGraphIso
    (fused (graph core1625) (root 10) 2 0) DegreeTwoThreeSpectrum2623.graph fusedMap1625swap=true := by decide +kernel
theorem certified1625swap : Certified (graph core1625) (root 10) 2 0 :=
  of_native_maps core1625 DegreeTwoThreeSpectrum3362.graph DegreeTwoThreeSpectrum2623.graph
    sourceMap1625swap fusedMap1625swap sourceMap1625swap_checked fusedMap1625swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1625
#print axioms sourceMap1625swap_checked
#print axioms fusedMap1625swap_checked
#print axioms certified1625swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
