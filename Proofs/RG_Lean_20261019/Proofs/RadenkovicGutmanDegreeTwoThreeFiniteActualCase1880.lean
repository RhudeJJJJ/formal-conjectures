/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1880 : Family 10 := level10.get ⟨1329,by decide⟩
def sourceMap1880 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1880 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1880_checked : acceptsGraphIso
    (source (graph core1880) (root 10) 0 2) DegreeTwoThreeSpectrum3504.graph sourceMap1880=true := by decide +kernel
theorem fusedMap1880_checked : acceptsGraphIso
    (fused (graph core1880) (root 10) 0 2) DegreeTwoThreeSpectrum3505.graph fusedMap1880=true := by decide +kernel
theorem certified1880 : Certified (graph core1880) (root 10) 0 2 :=
  of_native_maps core1880 DegreeTwoThreeSpectrum3504.graph DegreeTwoThreeSpectrum3505.graph
    sourceMap1880 fusedMap1880 sourceMap1880_checked fusedMap1880_checked
    DegreeTwoThreeFiniteComparisons.comparison1880
#print axioms sourceMap1880_checked
#print axioms fusedMap1880_checked
#print axioms certified1880
def sourceMap1880swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1880swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1880swap_checked : acceptsGraphIso
    (source (graph core1880) (root 10) 2 0) DegreeTwoThreeSpectrum3504.graph sourceMap1880swap=true := by decide +kernel
theorem fusedMap1880swap_checked : acceptsGraphIso
    (fused (graph core1880) (root 10) 2 0) DegreeTwoThreeSpectrum3505.graph fusedMap1880swap=true := by decide +kernel
theorem certified1880swap : Certified (graph core1880) (root 10) 2 0 :=
  of_native_maps core1880 DegreeTwoThreeSpectrum3504.graph DegreeTwoThreeSpectrum3505.graph
    sourceMap1880swap fusedMap1880swap sourceMap1880swap_checked fusedMap1880swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1880
#print axioms sourceMap1880swap_checked
#print axioms fusedMap1880swap_checked
#print axioms certified1880swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
