/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1665 : Family 10 := level10.get ⟨791,by decide⟩
def sourceMap1665 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,11,12,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1665 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1665_checked : acceptsGraphIso
    (source (graph core1665) (root 10) 0 2) DegreeTwoThreeSpectrum3581.graph sourceMap1665=true := by decide +kernel
theorem fusedMap1665_checked : acceptsGraphIso
    (fused (graph core1665) (root 10) 0 2) DegreeTwoThreeSpectrum2756.graph fusedMap1665=true := by decide +kernel
theorem certified1665 : Certified (graph core1665) (root 10) 0 2 :=
  of_native_maps core1665 DegreeTwoThreeSpectrum3581.graph DegreeTwoThreeSpectrum2756.graph
    sourceMap1665 fusedMap1665 sourceMap1665_checked fusedMap1665_checked
    DegreeTwoThreeFiniteComparisons.comparison1665
#print axioms sourceMap1665_checked
#print axioms fusedMap1665_checked
#print axioms certified1665
def sourceMap1665swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,11,8,9,10,12] (sourceLabel 10 2 0 v)
def fusedMap1665swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1665swap_checked : acceptsGraphIso
    (source (graph core1665) (root 10) 2 0) DegreeTwoThreeSpectrum3581.graph sourceMap1665swap=true := by decide +kernel
theorem fusedMap1665swap_checked : acceptsGraphIso
    (fused (graph core1665) (root 10) 2 0) DegreeTwoThreeSpectrum2756.graph fusedMap1665swap=true := by decide +kernel
theorem certified1665swap : Certified (graph core1665) (root 10) 2 0 :=
  of_native_maps core1665 DegreeTwoThreeSpectrum3581.graph DegreeTwoThreeSpectrum2756.graph
    sourceMap1665swap fusedMap1665swap sourceMap1665swap_checked fusedMap1665swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1665
#print axioms sourceMap1665swap_checked
#print axioms fusedMap1665swap_checked
#print axioms certified1665swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
