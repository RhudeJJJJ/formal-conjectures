/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1140 : Family 8 := level8.get ⟨147,by decide⟩
def sourceMap1140 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (sourceLabel 8 0 2 v)
def fusedMap1140 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,11,12,7,8,9,10] (fusedLabel 8 0 2 v)
theorem sourceMap1140_checked : acceptsGraphIso
    (source (graph core1140) (root 8) 0 2) DegreeOneSmallSpectrum1387.graph sourceMap1140=true := by decide +kernel
theorem fusedMap1140_checked : acceptsGraphIso
    (fused (graph core1140) (root 8) 0 2) DegreeOneSmallSpectrum1392.graph fusedMap1140=true := by decide +kernel
theorem certified1140 : Certified (graph core1140) (root 8) 0 2 :=
  of_native_maps core1140 DegreeOneSmallSpectrum1387.graph DegreeOneSmallSpectrum1392.graph
    sourceMap1140 fusedMap1140 sourceMap1140_checked fusedMap1140_checked
    DegreeTwoThreeFiniteComparisons.comparison1140
#print axioms sourceMap1140_checked
#print axioms fusedMap1140_checked
#print axioms certified1140
def sourceMap1140swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9,12] (sourceLabel 8 2 0 v)
def fusedMap1140swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,11,12,7,8,9,10] (fusedLabel 8 2 0 v)
theorem sourceMap1140swap_checked : acceptsGraphIso
    (source (graph core1140) (root 8) 2 0) DegreeOneSmallSpectrum1387.graph sourceMap1140swap=true := by decide +kernel
theorem fusedMap1140swap_checked : acceptsGraphIso
    (fused (graph core1140) (root 8) 2 0) DegreeOneSmallSpectrum1392.graph fusedMap1140swap=true := by decide +kernel
theorem certified1140swap : Certified (graph core1140) (root 8) 2 0 :=
  of_native_maps core1140 DegreeOneSmallSpectrum1387.graph DegreeOneSmallSpectrum1392.graph
    sourceMap1140swap fusedMap1140swap sourceMap1140swap_checked fusedMap1140swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1140
#print axioms sourceMap1140swap_checked
#print axioms fusedMap1140swap_checked
#print axioms certified1140swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
