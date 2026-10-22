/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1561 : Family 10 := level10.get ⟨482,by decide⟩
def sourceMap1561 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,8,9,5,6,7,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1561 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,6,7,2,3,4,5] (fusedLabel 10 0 2 v)
theorem sourceMap1561_checked : acceptsGraphIso
    (source (graph core1561) (root 10) 0 2) DegreeTwoThreeSpectrum2845.graph sourceMap1561=true := by decide +kernel
theorem fusedMap1561_checked : acceptsGraphIso
    (fused (graph core1561) (root 10) 0 2) DegreeTwoThreeSpectrum2982.graph fusedMap1561=true := by decide +kernel
theorem certified1561 : Certified (graph core1561) (root 10) 0 2 :=
  of_native_maps core1561 DegreeTwoThreeSpectrum2845.graph DegreeTwoThreeSpectrum2982.graph
    sourceMap1561 fusedMap1561 sourceMap1561_checked fusedMap1561_checked
    DegreeTwoThreeFiniteComparisons.comparison1561
#print axioms sourceMap1561_checked
#print axioms fusedMap1561_checked
#print axioms certified1561
def sourceMap1561swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,8,9,5,6,2,3,4,7] (sourceLabel 10 2 0 v)
def fusedMap1561swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,6,7,2,3,4,5] (fusedLabel 10 2 0 v)
theorem sourceMap1561swap_checked : acceptsGraphIso
    (source (graph core1561) (root 10) 2 0) DegreeTwoThreeSpectrum2845.graph sourceMap1561swap=true := by decide +kernel
theorem fusedMap1561swap_checked : acceptsGraphIso
    (fused (graph core1561) (root 10) 2 0) DegreeTwoThreeSpectrum2982.graph fusedMap1561swap=true := by decide +kernel
theorem certified1561swap : Certified (graph core1561) (root 10) 2 0 :=
  of_native_maps core1561 DegreeTwoThreeSpectrum2845.graph DegreeTwoThreeSpectrum2982.graph
    sourceMap1561swap fusedMap1561swap sourceMap1561swap_checked fusedMap1561swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1561
#print axioms sourceMap1561swap_checked
#print axioms fusedMap1561swap_checked
#print axioms certified1561swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
