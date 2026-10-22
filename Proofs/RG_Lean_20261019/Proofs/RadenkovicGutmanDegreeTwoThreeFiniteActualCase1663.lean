/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1663 : Family 10 := level10.get ⟨785,by decide⟩
def sourceMap1663 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,13,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1663 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1663_checked : acceptsGraphIso
    (source (graph core1663) (root 10) 0 2) DegreeTwoThreeSpectrum3573.graph sourceMap1663=true := by decide +kernel
theorem fusedMap1663_checked : acceptsGraphIso
    (fused (graph core1663) (root 10) 0 2) DegreeTwoThreeSpectrum2750.graph fusedMap1663=true := by decide +kernel
theorem certified1663 : Certified (graph core1663) (root 10) 0 2 :=
  of_native_maps core1663 DegreeTwoThreeSpectrum3573.graph DegreeTwoThreeSpectrum2750.graph
    sourceMap1663 fusedMap1663 sourceMap1663_checked fusedMap1663_checked
    DegreeTwoThreeFiniteComparisons.comparison1663
#print axioms sourceMap1663_checked
#print axioms fusedMap1663_checked
#print axioms certified1663
def sourceMap1663swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,9,10,11,13] (sourceLabel 10 2 0 v)
def fusedMap1663swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1663swap_checked : acceptsGraphIso
    (source (graph core1663) (root 10) 2 0) DegreeTwoThreeSpectrum3573.graph sourceMap1663swap=true := by decide +kernel
theorem fusedMap1663swap_checked : acceptsGraphIso
    (fused (graph core1663) (root 10) 2 0) DegreeTwoThreeSpectrum2750.graph fusedMap1663swap=true := by decide +kernel
theorem certified1663swap : Certified (graph core1663) (root 10) 2 0 :=
  of_native_maps core1663 DegreeTwoThreeSpectrum3573.graph DegreeTwoThreeSpectrum2750.graph
    sourceMap1663swap fusedMap1663swap sourceMap1663swap_checked fusedMap1663swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1663
#print axioms sourceMap1663swap_checked
#print axioms fusedMap1663swap_checked
#print axioms certified1663swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
