/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1752 : Family 10 := level10.get ⟨1011,by decide⟩
def sourceMap1752 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1752 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1752_checked : acceptsGraphIso
    (source (graph core1752) (root 10) 0 2) DegreeTwoThreeSpectrum3027.graph sourceMap1752=true := by decide +kernel
theorem fusedMap1752_checked : acceptsGraphIso
    (fused (graph core1752) (root 10) 0 2) DegreeTwoThreeSpectrum3028.graph fusedMap1752=true := by decide +kernel
theorem certified1752 : Certified (graph core1752) (root 10) 0 2 :=
  of_native_maps core1752 DegreeTwoThreeSpectrum3027.graph DegreeTwoThreeSpectrum3028.graph
    sourceMap1752 fusedMap1752 sourceMap1752_checked fusedMap1752_checked
    DegreeTwoThreeFiniteComparisons.comparison1752
#print axioms sourceMap1752_checked
#print axioms fusedMap1752_checked
#print axioms certified1752
def sourceMap1752swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1752swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1752swap_checked : acceptsGraphIso
    (source (graph core1752) (root 10) 2 0) DegreeTwoThreeSpectrum3027.graph sourceMap1752swap=true := by decide +kernel
theorem fusedMap1752swap_checked : acceptsGraphIso
    (fused (graph core1752) (root 10) 2 0) DegreeTwoThreeSpectrum3028.graph fusedMap1752swap=true := by decide +kernel
theorem certified1752swap : Certified (graph core1752) (root 10) 2 0 :=
  of_native_maps core1752 DegreeTwoThreeSpectrum3027.graph DegreeTwoThreeSpectrum3028.graph
    sourceMap1752swap fusedMap1752swap sourceMap1752swap_checked fusedMap1752swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1752
#print axioms sourceMap1752swap_checked
#print axioms fusedMap1752swap_checked
#print axioms certified1752swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
