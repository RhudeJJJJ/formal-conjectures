/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1515 : Family 10 := level10.get ⟨346,by decide⟩
def sourceMap1515 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1515 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1515_checked : acceptsGraphIso
    (source (graph core1515) (root 10) 0 2) DegreeTwoThreeSpectrum2781.graph sourceMap1515=true := by decide +kernel
theorem fusedMap1515_checked : acceptsGraphIso
    (fused (graph core1515) (root 10) 0 2) DegreeTwoThreeSpectrum2783.graph fusedMap1515=true := by decide +kernel
theorem certified1515 : Certified (graph core1515) (root 10) 0 2 :=
  of_native_maps core1515 DegreeTwoThreeSpectrum2781.graph DegreeTwoThreeSpectrum2783.graph
    sourceMap1515 fusedMap1515 sourceMap1515_checked fusedMap1515_checked
    DegreeTwoThreeFiniteComparisons.comparison1515
#print axioms sourceMap1515_checked
#print axioms fusedMap1515_checked
#print axioms certified1515
def sourceMap1515swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1515swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1515swap_checked : acceptsGraphIso
    (source (graph core1515) (root 10) 2 0) DegreeTwoThreeSpectrum2781.graph sourceMap1515swap=true := by decide +kernel
theorem fusedMap1515swap_checked : acceptsGraphIso
    (fused (graph core1515) (root 10) 2 0) DegreeTwoThreeSpectrum2783.graph fusedMap1515swap=true := by decide +kernel
theorem certified1515swap : Certified (graph core1515) (root 10) 2 0 :=
  of_native_maps core1515 DegreeTwoThreeSpectrum2781.graph DegreeTwoThreeSpectrum2783.graph
    sourceMap1515swap fusedMap1515swap sourceMap1515swap_checked fusedMap1515swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1515
#print axioms sourceMap1515swap_checked
#print axioms fusedMap1515swap_checked
#print axioms certified1515swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
