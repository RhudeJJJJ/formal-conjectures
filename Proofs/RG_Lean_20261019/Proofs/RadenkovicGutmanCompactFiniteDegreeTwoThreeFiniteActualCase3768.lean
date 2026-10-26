/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3768 : Family 5 := level5.get ⟨4,by decide⟩
def sourceMap3768 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,7,5,6,8,9,10,11,12] (sourceLabel 5 1 4 v)
def fusedMap3768 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11,12] (fusedLabel 5 1 4 v)
theorem sourceMap3768_checked : acceptsGraphIso
    (source (graph core3768) (root 5) 1 4) DegreeOneSmallSpectrum969.graph sourceMap3768=true := by decide +kernel
theorem fusedMap3768_checked : acceptsGraphIso
    (fused (graph core3768) (root 5) 1 4) DegreeOneSmallSpectrum859.graph fusedMap3768=true := by decide +kernel
theorem certified3768 : Certified (graph core3768) (root 5) 1 4 :=
  of_native_maps core3768 DegreeOneSmallSpectrum969.graph DegreeOneSmallSpectrum859.graph
    sourceMap3768 fusedMap3768 sourceMap3768_checked fusedMap3768_checked
    DegreeTwoThreeFiniteComparisons.comparison3768
#print axioms sourceMap3768_checked
#print axioms fusedMap3768_checked
#print axioms certified3768
def sourceMap3768swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,7,8,9,10,11,12,5,6] (sourceLabel 5 4 1 v)
def fusedMap3768swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11,12] (fusedLabel 5 4 1 v)
theorem sourceMap3768swap_checked : acceptsGraphIso
    (source (graph core3768) (root 5) 4 1) DegreeOneSmallSpectrum969.graph sourceMap3768swap=true := by decide +kernel
theorem fusedMap3768swap_checked : acceptsGraphIso
    (fused (graph core3768) (root 5) 4 1) DegreeOneSmallSpectrum859.graph fusedMap3768swap=true := by decide +kernel
theorem certified3768swap : Certified (graph core3768) (root 5) 4 1 :=
  of_native_maps core3768 DegreeOneSmallSpectrum969.graph DegreeOneSmallSpectrum859.graph
    sourceMap3768swap fusedMap3768swap sourceMap3768swap_checked fusedMap3768swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3768
#print axioms sourceMap3768swap_checked
#print axioms fusedMap3768swap_checked
#print axioms certified3768swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
