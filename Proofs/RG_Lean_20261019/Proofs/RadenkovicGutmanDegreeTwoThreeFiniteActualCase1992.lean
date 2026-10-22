/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1992 : Family 10 := level10.get ⟨1600,by decide⟩
def sourceMap1992 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1992 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1992_checked : acceptsGraphIso
    (source (graph core1992) (root 10) 0 2) DegreeTwoThreeSpectrum3777.graph sourceMap1992=true := by decide +kernel
theorem fusedMap1992_checked : acceptsGraphIso
    (fused (graph core1992) (root 10) 0 2) DegreeTwoThreeSpectrum3113.graph fusedMap1992=true := by decide +kernel
theorem certified1992 : Certified (graph core1992) (root 10) 0 2 :=
  of_native_maps core1992 DegreeTwoThreeSpectrum3777.graph DegreeTwoThreeSpectrum3113.graph
    sourceMap1992 fusedMap1992 sourceMap1992_checked fusedMap1992_checked
    DegreeTwoThreeFiniteComparisons.comparison1992
#print axioms sourceMap1992_checked
#print axioms fusedMap1992_checked
#print axioms certified1992
def sourceMap1992swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1992swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1992swap_checked : acceptsGraphIso
    (source (graph core1992) (root 10) 2 0) DegreeTwoThreeSpectrum3777.graph sourceMap1992swap=true := by decide +kernel
theorem fusedMap1992swap_checked : acceptsGraphIso
    (fused (graph core1992) (root 10) 2 0) DegreeTwoThreeSpectrum3113.graph fusedMap1992swap=true := by decide +kernel
theorem certified1992swap : Certified (graph core1992) (root 10) 2 0 :=
  of_native_maps core1992 DegreeTwoThreeSpectrum3777.graph DegreeTwoThreeSpectrum3113.graph
    sourceMap1992swap fusedMap1992swap sourceMap1992swap_checked fusedMap1992swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1992
#print axioms sourceMap1992swap_checked
#print axioms fusedMap1992swap_checked
#print axioms certified1992swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
