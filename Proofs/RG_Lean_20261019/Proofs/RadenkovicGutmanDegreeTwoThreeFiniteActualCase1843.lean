/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1843 : Family 10 := level10.get ⟨1229,by decide⟩
def sourceMap1843 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1843 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,6,7,8,9] (fusedLabel 10 0 2 v)
theorem sourceMap1843_checked : acceptsGraphIso
    (source (graph core1843) (root 10) 0 2) DegreeTwoThreeSpectrum3352.graph sourceMap1843=true := by decide +kernel
theorem fusedMap1843_checked : acceptsGraphIso
    (fused (graph core1843) (root 10) 0 2) DegreeTwoThreeSpectrum3374.graph fusedMap1843=true := by decide +kernel
theorem certified1843 : Certified (graph core1843) (root 10) 0 2 :=
  of_native_maps core1843 DegreeTwoThreeSpectrum3352.graph DegreeTwoThreeSpectrum3374.graph
    sourceMap1843 fusedMap1843 sourceMap1843_checked fusedMap1843_checked
    DegreeTwoThreeFiniteComparisons.comparison1843
#print axioms sourceMap1843_checked
#print axioms fusedMap1843_checked
#print axioms certified1843
def sourceMap1843swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1843swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,6,7,8,9] (fusedLabel 10 2 0 v)
theorem sourceMap1843swap_checked : acceptsGraphIso
    (source (graph core1843) (root 10) 2 0) DegreeTwoThreeSpectrum3352.graph sourceMap1843swap=true := by decide +kernel
theorem fusedMap1843swap_checked : acceptsGraphIso
    (fused (graph core1843) (root 10) 2 0) DegreeTwoThreeSpectrum3374.graph fusedMap1843swap=true := by decide +kernel
theorem certified1843swap : Certified (graph core1843) (root 10) 2 0 :=
  of_native_maps core1843 DegreeTwoThreeSpectrum3352.graph DegreeTwoThreeSpectrum3374.graph
    sourceMap1843swap fusedMap1843swap sourceMap1843swap_checked fusedMap1843swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1843
#print axioms sourceMap1843swap_checked
#print axioms fusedMap1843swap_checked
#print axioms certified1843swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
