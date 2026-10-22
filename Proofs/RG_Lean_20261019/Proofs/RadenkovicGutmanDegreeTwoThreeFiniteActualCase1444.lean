/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1444 : Family 10 := level10.get ⟨81,by decide⟩
def sourceMap1444 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,14,12,13,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1444 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1444_checked : acceptsGraphIso
    (source (graph core1444) (root 10) 0 2) DegreeTwoThreeSpectrum2634.graph sourceMap1444=true := by decide +kernel
theorem fusedMap1444_checked : acceptsGraphIso
    (fused (graph core1444) (root 10) 0 2) DegreeTwoThreeSpectrum2341.graph fusedMap1444=true := by decide +kernel
theorem certified1444 : Certified (graph core1444) (root 10) 0 2 :=
  of_native_maps core1444 DegreeTwoThreeSpectrum2634.graph DegreeTwoThreeSpectrum2341.graph
    sourceMap1444 fusedMap1444 sourceMap1444_checked fusedMap1444_checked
    DegreeTwoThreeFiniteComparisons.comparison1444
#print axioms sourceMap1444_checked
#print axioms fusedMap1444_checked
#print axioms certified1444
def sourceMap1444swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,14,12,9,10,11,13] (sourceLabel 10 2 0 v)
def fusedMap1444swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1444swap_checked : acceptsGraphIso
    (source (graph core1444) (root 10) 2 0) DegreeTwoThreeSpectrum2634.graph sourceMap1444swap=true := by decide +kernel
theorem fusedMap1444swap_checked : acceptsGraphIso
    (fused (graph core1444) (root 10) 2 0) DegreeTwoThreeSpectrum2341.graph fusedMap1444swap=true := by decide +kernel
theorem certified1444swap : Certified (graph core1444) (root 10) 2 0 :=
  of_native_maps core1444 DegreeTwoThreeSpectrum2634.graph DegreeTwoThreeSpectrum2341.graph
    sourceMap1444swap fusedMap1444swap sourceMap1444swap_checked fusedMap1444swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1444
#print axioms sourceMap1444swap_checked
#print axioms fusedMap1444swap_checked
#print axioms certified1444swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
