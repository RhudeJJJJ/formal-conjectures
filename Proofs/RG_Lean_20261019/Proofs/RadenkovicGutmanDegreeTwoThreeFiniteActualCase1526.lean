/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1526 : Family 10 := level10.get ⟨380,by decide⟩
def sourceMap1526 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1526 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1526_checked : acceptsGraphIso
    (source (graph core1526) (root 10) 0 2) DegreeTwoThreeSpectrum2850.graph sourceMap1526=true := by decide +kernel
theorem fusedMap1526_checked : acceptsGraphIso
    (fused (graph core1526) (root 10) 0 2) DegreeTwoThreeSpectrum2855.graph fusedMap1526=true := by decide +kernel
theorem certified1526 : Certified (graph core1526) (root 10) 0 2 :=
  of_native_maps core1526 DegreeTwoThreeSpectrum2850.graph DegreeTwoThreeSpectrum2855.graph
    sourceMap1526 fusedMap1526 sourceMap1526_checked fusedMap1526_checked
    DegreeTwoThreeFiniteComparisons.comparison1526
#print axioms sourceMap1526_checked
#print axioms fusedMap1526_checked
#print axioms certified1526
def sourceMap1526swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1526swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1526swap_checked : acceptsGraphIso
    (source (graph core1526) (root 10) 2 0) DegreeTwoThreeSpectrum2850.graph sourceMap1526swap=true := by decide +kernel
theorem fusedMap1526swap_checked : acceptsGraphIso
    (fused (graph core1526) (root 10) 2 0) DegreeTwoThreeSpectrum2855.graph fusedMap1526swap=true := by decide +kernel
theorem certified1526swap : Certified (graph core1526) (root 10) 2 0 :=
  of_native_maps core1526 DegreeTwoThreeSpectrum2850.graph DegreeTwoThreeSpectrum2855.graph
    sourceMap1526swap fusedMap1526swap sourceMap1526swap_checked fusedMap1526swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1526
#print axioms sourceMap1526swap_checked
#print axioms fusedMap1526swap_checked
#print axioms certified1526swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
