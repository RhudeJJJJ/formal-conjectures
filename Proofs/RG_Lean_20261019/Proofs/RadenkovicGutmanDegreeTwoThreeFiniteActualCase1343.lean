/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1343 : Family 9 := level9.get ⟨466,by decide⟩
def sourceMap1343 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1343 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1343_checked : acceptsGraphIso
    (source (graph core1343) (root 9) 0 2) DegreeTwoThreeSpectrum2151.graph sourceMap1343=true := by decide +kernel
theorem fusedMap1343_checked : acceptsGraphIso
    (fused (graph core1343) (root 9) 0 2) DegreeTwoThreeSpectrum2152.graph fusedMap1343=true := by decide +kernel
theorem certified1343 : Certified (graph core1343) (root 9) 0 2 :=
  of_native_maps core1343 DegreeTwoThreeSpectrum2151.graph DegreeTwoThreeSpectrum2152.graph
    sourceMap1343 fusedMap1343 sourceMap1343_checked fusedMap1343_checked
    DegreeTwoThreeFiniteComparisons.comparison1343
#print axioms sourceMap1343_checked
#print axioms fusedMap1343_checked
#print axioms certified1343
def sourceMap1343swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1343swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1343swap_checked : acceptsGraphIso
    (source (graph core1343) (root 9) 2 0) DegreeTwoThreeSpectrum2151.graph sourceMap1343swap=true := by decide +kernel
theorem fusedMap1343swap_checked : acceptsGraphIso
    (fused (graph core1343) (root 9) 2 0) DegreeTwoThreeSpectrum2152.graph fusedMap1343swap=true := by decide +kernel
theorem certified1343swap : Certified (graph core1343) (root 9) 2 0 :=
  of_native_maps core1343 DegreeTwoThreeSpectrum2151.graph DegreeTwoThreeSpectrum2152.graph
    sourceMap1343swap fusedMap1343swap sourceMap1343swap_checked fusedMap1343swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1343
#print axioms sourceMap1343swap_checked
#print axioms fusedMap1343swap_checked
#print axioms certified1343swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
