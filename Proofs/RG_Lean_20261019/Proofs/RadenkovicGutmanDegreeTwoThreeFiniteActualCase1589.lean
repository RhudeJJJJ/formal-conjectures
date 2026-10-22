/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1589 : Family 10 := level10.get ⟨571,by decide⟩
def sourceMap1589 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1589 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1589_checked : acceptsGraphIso
    (source (graph core1589) (root 10) 0 2) DegreeTwoThreeSpectrum3197.graph sourceMap1589=true := by decide +kernel
theorem fusedMap1589_checked : acceptsGraphIso
    (fused (graph core1589) (root 10) 0 2) DegreeTwoThreeSpectrum2512.graph fusedMap1589=true := by decide +kernel
theorem certified1589 : Certified (graph core1589) (root 10) 0 2 :=
  of_native_maps core1589 DegreeTwoThreeSpectrum3197.graph DegreeTwoThreeSpectrum2512.graph
    sourceMap1589 fusedMap1589 sourceMap1589_checked fusedMap1589_checked
    DegreeTwoThreeFiniteComparisons.comparison1589
#print axioms sourceMap1589_checked
#print axioms fusedMap1589_checked
#print axioms certified1589
def sourceMap1589swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1589swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1589swap_checked : acceptsGraphIso
    (source (graph core1589) (root 10) 2 0) DegreeTwoThreeSpectrum3197.graph sourceMap1589swap=true := by decide +kernel
theorem fusedMap1589swap_checked : acceptsGraphIso
    (fused (graph core1589) (root 10) 2 0) DegreeTwoThreeSpectrum2512.graph fusedMap1589swap=true := by decide +kernel
theorem certified1589swap : Certified (graph core1589) (root 10) 2 0 :=
  of_native_maps core1589 DegreeTwoThreeSpectrum3197.graph DegreeTwoThreeSpectrum2512.graph
    sourceMap1589swap fusedMap1589swap sourceMap1589swap_checked fusedMap1589swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1589
#print axioms sourceMap1589swap_checked
#print axioms fusedMap1589swap_checked
#print axioms certified1589swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
