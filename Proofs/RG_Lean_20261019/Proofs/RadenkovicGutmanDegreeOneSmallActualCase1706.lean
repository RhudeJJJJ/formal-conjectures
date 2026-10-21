/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1706 : Family 9 := level9.get ⟨486,by decide⟩
def sourceMap1706 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1706 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1706_checked : acceptsGraphIso
    (source (graph core1706) (root 9) 0 1) DegreeOneSmallSpectrum1963.graph sourceMap1706=true := by decide +kernel
theorem fusedMap1706_checked : acceptsGraphIso
    (fused (graph core1706) (root 9) 0 1) DegreeOneSmallSpectrum1456.graph fusedMap1706=true := by decide +kernel
theorem certified1706 : Certified (graph core1706) (root 9) 0 1 :=
  of_native_maps core1706 DegreeOneSmallSpectrum1963.graph DegreeOneSmallSpectrum1456.graph
    sourceMap1706 fusedMap1706 sourceMap1706_checked fusedMap1706_checked
    DegreeOneSmallComparisons.comparison1706
#print axioms sourceMap1706_checked
#print axioms fusedMap1706_checked
#print axioms certified1706
def sourceMap1706swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1706swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1706swap_checked : acceptsGraphIso
    (source (graph core1706) (root 9) 1 0) DegreeOneSmallSpectrum1963.graph sourceMap1706swap=true := by decide +kernel
theorem fusedMap1706swap_checked : acceptsGraphIso
    (fused (graph core1706) (root 9) 1 0) DegreeOneSmallSpectrum1456.graph fusedMap1706swap=true := by decide +kernel
theorem certified1706swap : Certified (graph core1706) (root 9) 1 0 :=
  of_native_maps core1706 DegreeOneSmallSpectrum1963.graph DegreeOneSmallSpectrum1456.graph
    sourceMap1706swap fusedMap1706swap sourceMap1706swap_checked fusedMap1706swap_checked
    DegreeOneSmallComparisons.comparison1706
#print axioms sourceMap1706swap_checked
#print axioms fusedMap1706swap_checked
#print axioms certified1706swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
