/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1673 : Family 10 := level10.get ⟨811,by decide⟩
def sourceMap1673 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,13,14,10,11,12,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1673 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1673_checked : acceptsGraphIso
    (source (graph core1673) (root 10) 0 2) DegreeTwoThreeSpectrum3597.graph sourceMap1673=true := by decide +kernel
theorem fusedMap1673_checked : acceptsGraphIso
    (fused (graph core1673) (root 10) 0 2) DegreeTwoThreeSpectrum2782.graph fusedMap1673=true := by decide +kernel
theorem certified1673 : Certified (graph core1673) (root 10) 0 2 :=
  of_native_maps core1673 DegreeTwoThreeSpectrum3597.graph DegreeTwoThreeSpectrum2782.graph
    sourceMap1673 fusedMap1673 sourceMap1673_checked fusedMap1673_checked
    DegreeTwoThreeFiniteComparisons.comparison1673
#print axioms sourceMap1673_checked
#print axioms fusedMap1673_checked
#print axioms certified1673
def sourceMap1673swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,13,14,10,11,7,8,9,12] (sourceLabel 10 2 0 v)
def fusedMap1673swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1673swap_checked : acceptsGraphIso
    (source (graph core1673) (root 10) 2 0) DegreeTwoThreeSpectrum3597.graph sourceMap1673swap=true := by decide +kernel
theorem fusedMap1673swap_checked : acceptsGraphIso
    (fused (graph core1673) (root 10) 2 0) DegreeTwoThreeSpectrum2782.graph fusedMap1673swap=true := by decide +kernel
theorem certified1673swap : Certified (graph core1673) (root 10) 2 0 :=
  of_native_maps core1673 DegreeTwoThreeSpectrum3597.graph DegreeTwoThreeSpectrum2782.graph
    sourceMap1673swap fusedMap1673swap sourceMap1673swap_checked fusedMap1673swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1673
#print axioms sourceMap1673swap_checked
#print axioms fusedMap1673swap_checked
#print axioms certified1673swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
