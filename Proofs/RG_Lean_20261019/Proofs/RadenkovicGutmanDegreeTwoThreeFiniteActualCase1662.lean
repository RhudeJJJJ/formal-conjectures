/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1662 : Family 10 := level10.get ⟨782,by decide⟩
def sourceMap1662 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1662 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1662_checked : acceptsGraphIso
    (source (graph core1662) (root 10) 0 2) DegreeTwoThreeSpectrum3568.graph sourceMap1662=true := by decide +kernel
theorem fusedMap1662_checked : acceptsGraphIso
    (fused (graph core1662) (root 10) 0 2) DegreeTwoThreeSpectrum2748.graph fusedMap1662=true := by decide +kernel
theorem certified1662 : Certified (graph core1662) (root 10) 0 2 :=
  of_native_maps core1662 DegreeTwoThreeSpectrum3568.graph DegreeTwoThreeSpectrum2748.graph
    sourceMap1662 fusedMap1662 sourceMap1662_checked fusedMap1662_checked
    DegreeTwoThreeFiniteComparisons.comparison1662
#print axioms sourceMap1662_checked
#print axioms fusedMap1662_checked
#print axioms certified1662
def sourceMap1662swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1662swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1662swap_checked : acceptsGraphIso
    (source (graph core1662) (root 10) 2 0) DegreeTwoThreeSpectrum3568.graph sourceMap1662swap=true := by decide +kernel
theorem fusedMap1662swap_checked : acceptsGraphIso
    (fused (graph core1662) (root 10) 2 0) DegreeTwoThreeSpectrum2748.graph fusedMap1662swap=true := by decide +kernel
theorem certified1662swap : Certified (graph core1662) (root 10) 2 0 :=
  of_native_maps core1662 DegreeTwoThreeSpectrum3568.graph DegreeTwoThreeSpectrum2748.graph
    sourceMap1662swap fusedMap1662swap sourceMap1662swap_checked fusedMap1662swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1662
#print axioms sourceMap1662swap_checked
#print axioms fusedMap1662swap_checked
#print axioms certified1662swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
