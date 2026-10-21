/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1722 : Family 9 := level9.get ⟨509,by decide⟩
def sourceMap1722 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1722 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1722_checked : acceptsGraphIso
    (source (graph core1722) (root 9) 0 1) DegreeOneSmallSpectrum1971.graph sourceMap1722=true := by decide +kernel
theorem fusedMap1722_checked : acceptsGraphIso
    (fused (graph core1722) (root 9) 0 1) DegreeOneSmallSpectrum1492.graph fusedMap1722=true := by decide +kernel
theorem certified1722 : Certified (graph core1722) (root 9) 0 1 :=
  of_native_maps core1722 DegreeOneSmallSpectrum1971.graph DegreeOneSmallSpectrum1492.graph
    sourceMap1722 fusedMap1722 sourceMap1722_checked fusedMap1722_checked
    DegreeOneSmallComparisons.comparison1722
#print axioms sourceMap1722_checked
#print axioms fusedMap1722_checked
#print axioms certified1722
def sourceMap1722swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1722swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1722swap_checked : acceptsGraphIso
    (source (graph core1722) (root 9) 1 0) DegreeOneSmallSpectrum1971.graph sourceMap1722swap=true := by decide +kernel
theorem fusedMap1722swap_checked : acceptsGraphIso
    (fused (graph core1722) (root 9) 1 0) DegreeOneSmallSpectrum1492.graph fusedMap1722swap=true := by decide +kernel
theorem certified1722swap : Certified (graph core1722) (root 9) 1 0 :=
  of_native_maps core1722 DegreeOneSmallSpectrum1971.graph DegreeOneSmallSpectrum1492.graph
    sourceMap1722swap fusedMap1722swap sourceMap1722swap_checked fusedMap1722swap_checked
    DegreeOneSmallComparisons.comparison1722
#print axioms sourceMap1722swap_checked
#print axioms fusedMap1722swap_checked
#print axioms certified1722swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
