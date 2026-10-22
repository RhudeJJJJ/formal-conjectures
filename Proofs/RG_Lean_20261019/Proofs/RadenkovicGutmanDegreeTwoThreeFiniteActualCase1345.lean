/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1345 : Family 9 := level9.get ⟨470,by decide⟩
def sourceMap1345 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1345 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1345_checked : acceptsGraphIso
    (source (graph core1345) (root 9) 0 2) DegreeTwoThreeSpectrum2156.graph sourceMap1345=true := by decide +kernel
theorem fusedMap1345_checked : acceptsGraphIso
    (fused (graph core1345) (root 9) 0 2) DegreeTwoThreeSpectrum2157.graph fusedMap1345=true := by decide +kernel
theorem certified1345 : Certified (graph core1345) (root 9) 0 2 :=
  of_native_maps core1345 DegreeTwoThreeSpectrum2156.graph DegreeTwoThreeSpectrum2157.graph
    sourceMap1345 fusedMap1345 sourceMap1345_checked fusedMap1345_checked
    DegreeTwoThreeFiniteComparisons.comparison1345
#print axioms sourceMap1345_checked
#print axioms fusedMap1345_checked
#print axioms certified1345
def sourceMap1345swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1345swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1345swap_checked : acceptsGraphIso
    (source (graph core1345) (root 9) 2 0) DegreeTwoThreeSpectrum2156.graph sourceMap1345swap=true := by decide +kernel
theorem fusedMap1345swap_checked : acceptsGraphIso
    (fused (graph core1345) (root 9) 2 0) DegreeTwoThreeSpectrum2157.graph fusedMap1345swap=true := by decide +kernel
theorem certified1345swap : Certified (graph core1345) (root 9) 2 0 :=
  of_native_maps core1345 DegreeTwoThreeSpectrum2156.graph DegreeTwoThreeSpectrum2157.graph
    sourceMap1345swap fusedMap1345swap sourceMap1345swap_checked fusedMap1345swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1345
#print axioms sourceMap1345swap_checked
#print axioms fusedMap1345swap_checked
#print axioms certified1345swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
