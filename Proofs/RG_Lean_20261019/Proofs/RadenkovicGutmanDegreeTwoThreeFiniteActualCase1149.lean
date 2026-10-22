/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1149 : Family 8 := level8.get ⟨169,by decide⟩
def sourceMap1149 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,4,5,6,1,2,3] (sourceLabel 8 0 2 v)
def fusedMap1149 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,11,12,7,8,9,10] (fusedLabel 8 0 2 v)
theorem sourceMap1149_checked : acceptsGraphIso
    (source (graph core1149) (root 8) 0 2) DegreeOneSmallSpectrum1482.graph sourceMap1149=true := by decide +kernel
theorem fusedMap1149_checked : acceptsGraphIso
    (fused (graph core1149) (root 8) 0 2) DegreeOneSmallSpectrum1490.graph fusedMap1149=true := by decide +kernel
theorem certified1149 : Certified (graph core1149) (root 8) 0 2 :=
  of_native_maps core1149 DegreeOneSmallSpectrum1482.graph DegreeOneSmallSpectrum1490.graph
    sourceMap1149 fusedMap1149 sourceMap1149_checked fusedMap1149_checked
    DegreeTwoThreeFiniteComparisons.comparison1149
#print axioms sourceMap1149_checked
#print axioms fusedMap1149_checked
#print axioms certified1149
def sourceMap1149swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,4,5,1,2,3,6] (sourceLabel 8 2 0 v)
def fusedMap1149swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,11,12,7,8,9,10] (fusedLabel 8 2 0 v)
theorem sourceMap1149swap_checked : acceptsGraphIso
    (source (graph core1149) (root 8) 2 0) DegreeOneSmallSpectrum1482.graph sourceMap1149swap=true := by decide +kernel
theorem fusedMap1149swap_checked : acceptsGraphIso
    (fused (graph core1149) (root 8) 2 0) DegreeOneSmallSpectrum1490.graph fusedMap1149swap=true := by decide +kernel
theorem certified1149swap : Certified (graph core1149) (root 8) 2 0 :=
  of_native_maps core1149 DegreeOneSmallSpectrum1482.graph DegreeOneSmallSpectrum1490.graph
    sourceMap1149swap fusedMap1149swap sourceMap1149swap_checked fusedMap1149swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1149
#print axioms sourceMap1149swap_checked
#print axioms fusedMap1149swap_checked
#print axioms certified1149swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
