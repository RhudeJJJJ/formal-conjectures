/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1710 : Family 9 := level9.get ⟨491,by decide⟩
def sourceMap1710 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1710 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1710_checked : acceptsGraphIso
    (source (graph core1710) (root 9) 0 1) DegreeOneSmallSpectrum1965.graph sourceMap1710=true := by decide +kernel
theorem fusedMap1710_checked : acceptsGraphIso
    (fused (graph core1710) (root 9) 0 1) DegreeOneSmallSpectrum1464.graph fusedMap1710=true := by decide +kernel
theorem certified1710 : Certified (graph core1710) (root 9) 0 1 :=
  of_native_maps core1710 DegreeOneSmallSpectrum1965.graph DegreeOneSmallSpectrum1464.graph
    sourceMap1710 fusedMap1710 sourceMap1710_checked fusedMap1710_checked
    DegreeOneSmallComparisons.comparison1710
#print axioms sourceMap1710_checked
#print axioms fusedMap1710_checked
#print axioms certified1710
def sourceMap1710swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1710swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1710swap_checked : acceptsGraphIso
    (source (graph core1710) (root 9) 1 0) DegreeOneSmallSpectrum1965.graph sourceMap1710swap=true := by decide +kernel
theorem fusedMap1710swap_checked : acceptsGraphIso
    (fused (graph core1710) (root 9) 1 0) DegreeOneSmallSpectrum1464.graph fusedMap1710swap=true := by decide +kernel
theorem certified1710swap : Certified (graph core1710) (root 9) 1 0 :=
  of_native_maps core1710 DegreeOneSmallSpectrum1965.graph DegreeOneSmallSpectrum1464.graph
    sourceMap1710swap fusedMap1710swap sourceMap1710swap_checked fusedMap1710swap_checked
    DegreeOneSmallComparisons.comparison1710
#print axioms sourceMap1710swap_checked
#print axioms fusedMap1710swap_checked
#print axioms certified1710swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
