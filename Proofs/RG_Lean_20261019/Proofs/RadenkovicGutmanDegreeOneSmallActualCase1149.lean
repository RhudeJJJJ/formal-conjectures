/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1149 : Family 8 := level8.get ⟨192,by decide⟩
def sourceMap1149 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1149 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1149_checked : acceptsGraphIso
    (source (graph core1149) (root 8) 0 2) DegreeOneSmallSpectrum1577.graph sourceMap1149=true := by decide +kernel
theorem fusedMap1149_checked : acceptsGraphIso
    (fused (graph core1149) (root 8) 0 2) DegreeOneSmallSpectrum987.graph fusedMap1149=true := by decide +kernel
theorem certified1149 : Certified (graph core1149) (root 8) 0 2 :=
  of_native_maps core1149 DegreeOneSmallSpectrum1577.graph DegreeOneSmallSpectrum987.graph
    sourceMap1149 fusedMap1149 sourceMap1149_checked fusedMap1149_checked
    DegreeOneSmallComparisons.comparison1149
#print axioms sourceMap1149_checked
#print axioms fusedMap1149_checked
#print axioms certified1149
def sourceMap1149swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1149swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1149swap_checked : acceptsGraphIso
    (source (graph core1149) (root 8) 2 0) DegreeOneSmallSpectrum1577.graph sourceMap1149swap=true := by decide +kernel
theorem fusedMap1149swap_checked : acceptsGraphIso
    (fused (graph core1149) (root 8) 2 0) DegreeOneSmallSpectrum987.graph fusedMap1149swap=true := by decide +kernel
theorem certified1149swap : Certified (graph core1149) (root 8) 2 0 :=
  of_native_maps core1149 DegreeOneSmallSpectrum1577.graph DegreeOneSmallSpectrum987.graph
    sourceMap1149swap fusedMap1149swap sourceMap1149swap_checked fusedMap1149swap_checked
    DegreeOneSmallComparisons.comparison1149
#print axioms sourceMap1149swap_checked
#print axioms fusedMap1149swap_checked
#print axioms certified1149swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
