/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1631 : Family 10 := level10.get ⟨690,by decide⟩
def sourceMap1631 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1631 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1631_checked : acceptsGraphIso
    (source (graph core1631) (root 10) 0 2) DegreeTwoThreeSpectrum3399.graph sourceMap1631=true := by decide +kernel
theorem fusedMap1631_checked : acceptsGraphIso
    (fused (graph core1631) (root 10) 0 2) DegreeTwoThreeSpectrum2650.graph fusedMap1631=true := by decide +kernel
theorem certified1631 : Certified (graph core1631) (root 10) 0 2 :=
  of_native_maps core1631 DegreeTwoThreeSpectrum3399.graph DegreeTwoThreeSpectrum2650.graph
    sourceMap1631 fusedMap1631 sourceMap1631_checked fusedMap1631_checked
    DegreeTwoThreeFiniteComparisons.comparison1631
#print axioms sourceMap1631_checked
#print axioms fusedMap1631_checked
#print axioms certified1631
def sourceMap1631swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1631swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1631swap_checked : acceptsGraphIso
    (source (graph core1631) (root 10) 2 0) DegreeTwoThreeSpectrum3399.graph sourceMap1631swap=true := by decide +kernel
theorem fusedMap1631swap_checked : acceptsGraphIso
    (fused (graph core1631) (root 10) 2 0) DegreeTwoThreeSpectrum2650.graph fusedMap1631swap=true := by decide +kernel
theorem certified1631swap : Certified (graph core1631) (root 10) 2 0 :=
  of_native_maps core1631 DegreeTwoThreeSpectrum3399.graph DegreeTwoThreeSpectrum2650.graph
    sourceMap1631swap fusedMap1631swap sourceMap1631swap_checked fusedMap1631swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1631
#print axioms sourceMap1631swap_checked
#print axioms fusedMap1631swap_checked
#print axioms certified1631swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
