/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1120 : Family 8 := level8.get ⟨91,by decide⟩
def sourceMap1120 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,2,3,4,8,5,6,7] (sourceLabel 8 0 2 v)
def fusedMap1120 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,5,6,7,1,2,3,4] (fusedLabel 8 0 2 v)
theorem sourceMap1120_checked : acceptsGraphIso
    (source (graph core1120) (root 8) 0 2) DegreeOneSmallSpectrum1459.graph sourceMap1120=true := by decide +kernel
theorem fusedMap1120_checked : acceptsGraphIso
    (fused (graph core1120) (root 8) 0 2) DegreeOneSmallSpectrum967.graph fusedMap1120=true := by decide +kernel
theorem certified1120 : Certified (graph core1120) (root 8) 0 2 :=
  of_native_maps core1120 DegreeOneSmallSpectrum1459.graph DegreeOneSmallSpectrum967.graph
    sourceMap1120 fusedMap1120 sourceMap1120_checked fusedMap1120_checked
    DegreeTwoThreeFiniteComparisons.comparison1120
#print axioms sourceMap1120_checked
#print axioms fusedMap1120_checked
#print axioms certified1120
def sourceMap1120swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,2,3,4,5,6,7,8] (sourceLabel 8 2 0 v)
def fusedMap1120swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,5,6,7,1,2,3,4] (fusedLabel 8 2 0 v)
theorem sourceMap1120swap_checked : acceptsGraphIso
    (source (graph core1120) (root 8) 2 0) DegreeOneSmallSpectrum1459.graph sourceMap1120swap=true := by decide +kernel
theorem fusedMap1120swap_checked : acceptsGraphIso
    (fused (graph core1120) (root 8) 2 0) DegreeOneSmallSpectrum967.graph fusedMap1120swap=true := by decide +kernel
theorem certified1120swap : Certified (graph core1120) (root 8) 2 0 :=
  of_native_maps core1120 DegreeOneSmallSpectrum1459.graph DegreeOneSmallSpectrum967.graph
    sourceMap1120swap fusedMap1120swap sourceMap1120swap_checked fusedMap1120swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1120
#print axioms sourceMap1120swap_checked
#print axioms fusedMap1120swap_checked
#print axioms certified1120swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
