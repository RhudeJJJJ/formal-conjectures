/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1714 : Family 9 := level9.get ⟨494,by decide⟩
def sourceMap1714 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1714 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1714_checked : acceptsGraphIso
    (source (graph core1714) (root 9) 0 1) DegreeOneSmallSpectrum1967.graph sourceMap1714=true := by decide +kernel
theorem fusedMap1714_checked : acceptsGraphIso
    (fused (graph core1714) (root 9) 0 1) DegreeOneSmallSpectrum1468.graph fusedMap1714=true := by decide +kernel
theorem certified1714 : Certified (graph core1714) (root 9) 0 1 :=
  of_native_maps core1714 DegreeOneSmallSpectrum1967.graph DegreeOneSmallSpectrum1468.graph
    sourceMap1714 fusedMap1714 sourceMap1714_checked fusedMap1714_checked
    DegreeOneSmallComparisons.comparison1714
#print axioms sourceMap1714_checked
#print axioms fusedMap1714_checked
#print axioms certified1714
def sourceMap1714swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1714swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1714swap_checked : acceptsGraphIso
    (source (graph core1714) (root 9) 1 0) DegreeOneSmallSpectrum1967.graph sourceMap1714swap=true := by decide +kernel
theorem fusedMap1714swap_checked : acceptsGraphIso
    (fused (graph core1714) (root 9) 1 0) DegreeOneSmallSpectrum1468.graph fusedMap1714swap=true := by decide +kernel
theorem certified1714swap : Certified (graph core1714) (root 9) 1 0 :=
  of_native_maps core1714 DegreeOneSmallSpectrum1967.graph DegreeOneSmallSpectrum1468.graph
    sourceMap1714swap fusedMap1714swap sourceMap1714swap_checked fusedMap1714swap_checked
    DegreeOneSmallComparisons.comparison1714
#print axioms sourceMap1714swap_checked
#print axioms fusedMap1714swap_checked
#print axioms certified1714swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
