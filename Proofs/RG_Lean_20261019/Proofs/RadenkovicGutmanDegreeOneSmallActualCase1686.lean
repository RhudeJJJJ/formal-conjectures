/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1686 : Family 9 := level9.get ⟨447,by decide⟩
def sourceMap1686 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,9,7,8] (sourceLabel 9 0 1 v)
def fusedMap1686 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1686_checked : acceptsGraphIso
    (source (graph core1686) (root 9) 0 1) DegreeOneSmallSpectrum1947.graph sourceMap1686=true := by decide +kernel
theorem fusedMap1686_checked : acceptsGraphIso
    (fused (graph core1686) (root 9) 0 1) DegreeOneSmallSpectrum1366.graph fusedMap1686=true := by decide +kernel
theorem certified1686 : Certified (graph core1686) (root 9) 0 1 :=
  of_native_maps core1686 DegreeOneSmallSpectrum1947.graph DegreeOneSmallSpectrum1366.graph
    sourceMap1686 fusedMap1686 sourceMap1686_checked fusedMap1686_checked
    DegreeOneSmallComparisons.comparison1686
#print axioms sourceMap1686_checked
#print axioms fusedMap1686_checked
#print axioms certified1686
def sourceMap1686swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (sourceLabel 9 1 0 v)
def fusedMap1686swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1686swap_checked : acceptsGraphIso
    (source (graph core1686) (root 9) 1 0) DegreeOneSmallSpectrum1947.graph sourceMap1686swap=true := by decide +kernel
theorem fusedMap1686swap_checked : acceptsGraphIso
    (fused (graph core1686) (root 9) 1 0) DegreeOneSmallSpectrum1366.graph fusedMap1686swap=true := by decide +kernel
theorem certified1686swap : Certified (graph core1686) (root 9) 1 0 :=
  of_native_maps core1686 DegreeOneSmallSpectrum1947.graph DegreeOneSmallSpectrum1366.graph
    sourceMap1686swap fusedMap1686swap sourceMap1686swap_checked fusedMap1686swap_checked
    DegreeOneSmallComparisons.comparison1686
#print axioms sourceMap1686swap_checked
#print axioms fusedMap1686swap_checked
#print axioms certified1686swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
