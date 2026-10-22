/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1323 : Family 9 := level9.get ⟨410,by decide⟩
def sourceMap1323 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![5,0,1,2,3,4,9,10,11,12,13,6,7,8] (sourceLabel 9 0 2 v)
def fusedMap1323 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,6,7,8,9] (fusedLabel 9 0 2 v)
theorem sourceMap1323_checked : acceptsGraphIso
    (source (graph core1323) (root 9) 0 2) DegreeTwoThreeSpectrum2069.graph sourceMap1323=true := by decide +kernel
theorem fusedMap1323_checked : acceptsGraphIso
    (fused (graph core1323) (root 9) 0 2) DegreeTwoThreeSpectrum2078.graph fusedMap1323=true := by decide +kernel
theorem certified1323 : Certified (graph core1323) (root 9) 0 2 :=
  of_native_maps core1323 DegreeTwoThreeSpectrum2069.graph DegreeTwoThreeSpectrum2078.graph
    sourceMap1323 fusedMap1323 sourceMap1323_checked fusedMap1323_checked
    DegreeTwoThreeFiniteComparisons.comparison1323
#print axioms sourceMap1323_checked
#print axioms fusedMap1323_checked
#print axioms certified1323
def sourceMap1323swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![5,0,1,2,3,4,9,10,11,12,6,7,8,13] (sourceLabel 9 2 0 v)
def fusedMap1323swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,6,7,8,9] (fusedLabel 9 2 0 v)
theorem sourceMap1323swap_checked : acceptsGraphIso
    (source (graph core1323) (root 9) 2 0) DegreeTwoThreeSpectrum2069.graph sourceMap1323swap=true := by decide +kernel
theorem fusedMap1323swap_checked : acceptsGraphIso
    (fused (graph core1323) (root 9) 2 0) DegreeTwoThreeSpectrum2078.graph fusedMap1323swap=true := by decide +kernel
theorem certified1323swap : Certified (graph core1323) (root 9) 2 0 :=
  of_native_maps core1323 DegreeTwoThreeSpectrum2069.graph DegreeTwoThreeSpectrum2078.graph
    sourceMap1323swap fusedMap1323swap sourceMap1323swap_checked fusedMap1323swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1323
#print axioms sourceMap1323swap_checked
#print axioms fusedMap1323swap_checked
#print axioms certified1323swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
