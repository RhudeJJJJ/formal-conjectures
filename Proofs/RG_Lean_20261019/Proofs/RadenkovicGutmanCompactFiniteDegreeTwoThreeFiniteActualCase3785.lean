/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3785 : Family 6 := level6.get ⟨33,by decide⟩
def sourceMap3785 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13] (sourceLabel 6 1 4 v)
def fusedMap3785 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 1 4 v)
theorem sourceMap3785_checked : acceptsGraphIso
    (source (graph core3785) (root 6) 1 4) DegreeTwoThreeSpectrum2182.graph sourceMap3785=true := by decide +kernel
theorem fusedMap3785_checked : acceptsGraphIso
    (fused (graph core3785) (root 6) 1 4) DegreeTwoThreeSpectrum1861.graph fusedMap3785=true := by decide +kernel
theorem certified3785 : Certified (graph core3785) (root 6) 1 4 :=
  of_native_maps core3785 DegreeTwoThreeSpectrum2182.graph DegreeTwoThreeSpectrum1861.graph
    sourceMap3785 fusedMap3785 sourceMap3785_checked fusedMap3785_checked
    DegreeTwoThreeFiniteComparisons.comparison3785
#print axioms sourceMap3785_checked
#print axioms fusedMap3785_checked
#print axioms certified3785
def sourceMap3785swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 2) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,10,11,12,13,8,9] (sourceLabel 6 4 1 v)
def fusedMap3785swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 4 1 v)
theorem sourceMap3785swap_checked : acceptsGraphIso
    (source (graph core3785) (root 6) 4 1) DegreeTwoThreeSpectrum2182.graph sourceMap3785swap=true := by decide +kernel
theorem fusedMap3785swap_checked : acceptsGraphIso
    (fused (graph core3785) (root 6) 4 1) DegreeTwoThreeSpectrum1861.graph fusedMap3785swap=true := by decide +kernel
theorem certified3785swap : Certified (graph core3785) (root 6) 4 1 :=
  of_native_maps core3785 DegreeTwoThreeSpectrum2182.graph DegreeTwoThreeSpectrum1861.graph
    sourceMap3785swap fusedMap3785swap sourceMap3785swap_checked fusedMap3785swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3785
#print axioms sourceMap3785swap_checked
#print axioms fusedMap3785swap_checked
#print axioms certified3785swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
