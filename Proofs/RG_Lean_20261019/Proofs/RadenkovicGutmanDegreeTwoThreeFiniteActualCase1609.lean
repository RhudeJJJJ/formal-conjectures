/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1609 : Family 10 := level10.get ⟨631,by decide⟩
def sourceMap1609 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1609 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1609_checked : acceptsGraphIso
    (source (graph core1609) (root 10) 0 2) DegreeTwoThreeSpectrum3321.graph sourceMap1609=true := by decide +kernel
theorem fusedMap1609_checked : acceptsGraphIso
    (fused (graph core1609) (root 10) 0 2) DegreeTwoThreeSpectrum2577.graph fusedMap1609=true := by decide +kernel
theorem certified1609 : Certified (graph core1609) (root 10) 0 2 :=
  of_native_maps core1609 DegreeTwoThreeSpectrum3321.graph DegreeTwoThreeSpectrum2577.graph
    sourceMap1609 fusedMap1609 sourceMap1609_checked fusedMap1609_checked
    DegreeTwoThreeFiniteComparisons.comparison1609
#print axioms sourceMap1609_checked
#print axioms fusedMap1609_checked
#print axioms certified1609
def sourceMap1609swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1609swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1609swap_checked : acceptsGraphIso
    (source (graph core1609) (root 10) 2 0) DegreeTwoThreeSpectrum3321.graph sourceMap1609swap=true := by decide +kernel
theorem fusedMap1609swap_checked : acceptsGraphIso
    (fused (graph core1609) (root 10) 2 0) DegreeTwoThreeSpectrum2577.graph fusedMap1609swap=true := by decide +kernel
theorem certified1609swap : Certified (graph core1609) (root 10) 2 0 :=
  of_native_maps core1609 DegreeTwoThreeSpectrum3321.graph DegreeTwoThreeSpectrum2577.graph
    sourceMap1609swap fusedMap1609swap sourceMap1609swap_checked fusedMap1609swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1609
#print axioms sourceMap1609swap_checked
#print axioms fusedMap1609swap_checked
#print axioms certified1609swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
