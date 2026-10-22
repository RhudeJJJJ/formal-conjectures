/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1611 : Family 10 := level10.get ⟨638,by decide⟩
def sourceMap1611 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,13,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1611 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1611_checked : acceptsGraphIso
    (source (graph core1611) (root 10) 0 2) DegreeTwoThreeSpectrum3333.graph sourceMap1611=true := by decide +kernel
theorem fusedMap1611_checked : acceptsGraphIso
    (fused (graph core1611) (root 10) 0 2) DegreeTwoThreeSpectrum2581.graph fusedMap1611=true := by decide +kernel
theorem certified1611 : Certified (graph core1611) (root 10) 0 2 :=
  of_native_maps core1611 DegreeTwoThreeSpectrum3333.graph DegreeTwoThreeSpectrum2581.graph
    sourceMap1611 fusedMap1611 sourceMap1611_checked fusedMap1611_checked
    DegreeTwoThreeFiniteComparisons.comparison1611
#print axioms sourceMap1611_checked
#print axioms fusedMap1611_checked
#print axioms certified1611
def sourceMap1611swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,9,10,11,13] (sourceLabel 10 2 0 v)
def fusedMap1611swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1611swap_checked : acceptsGraphIso
    (source (graph core1611) (root 10) 2 0) DegreeTwoThreeSpectrum3333.graph sourceMap1611swap=true := by decide +kernel
theorem fusedMap1611swap_checked : acceptsGraphIso
    (fused (graph core1611) (root 10) 2 0) DegreeTwoThreeSpectrum2581.graph fusedMap1611swap=true := by decide +kernel
theorem certified1611swap : Certified (graph core1611) (root 10) 2 0 :=
  of_native_maps core1611 DegreeTwoThreeSpectrum3333.graph DegreeTwoThreeSpectrum2581.graph
    sourceMap1611swap fusedMap1611swap sourceMap1611swap_checked fusedMap1611swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1611
#print axioms sourceMap1611swap_checked
#print axioms fusedMap1611swap_checked
#print axioms certified1611swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
