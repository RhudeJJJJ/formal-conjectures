/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0049 : Family 2 := level2.get ⟨0,by decide⟩
def sourceMap0049 : (Vertices 2 ⊕ Fin 3 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,5,6,2,3,4,0,7,8,9,10,11] (sourceLabel 2 2 5 v)
def fusedMap0049 : (Vertices 2 ⊕ Fin 9) → Fin 12 :=
  fun v => ![3,4,5,2,1,0,6,7,8,9,10,11] (fusedLabel 2 2 5 v)
theorem sourceMap0049_checked : acceptsGraphIso
    (source (graph core0049) (root 2) 2 5) DegreeOneSmallSpectrum387.graph sourceMap0049=true := by decide +kernel
theorem fusedMap0049_checked : acceptsGraphIso
    (fused (graph core0049) (root 2) 2 5) DegreeOneSmallSpectrum369.graph fusedMap0049=true := by decide +kernel
theorem certified0049 : Certified (graph core0049) (root 2) 2 5 :=
  of_native_maps core0049 DegreeOneSmallSpectrum387.graph DegreeOneSmallSpectrum369.graph
    sourceMap0049 fusedMap0049 sourceMap0049_checked fusedMap0049_checked
    DegreeOneSmallComparisons.comparison0049
#print axioms sourceMap0049_checked
#print axioms fusedMap0049_checked
#print axioms certified0049
def sourceMap0049swap : (Vertices 2 ⊕ Fin 6 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,5,6,0,7,8,9,10,11,2,3,4] (sourceLabel 2 5 2 v)
def fusedMap0049swap : (Vertices 2 ⊕ Fin 9) → Fin 12 :=
  fun v => ![3,4,5,2,1,0,6,7,8,9,10,11] (fusedLabel 2 5 2 v)
theorem sourceMap0049swap_checked : acceptsGraphIso
    (source (graph core0049) (root 2) 5 2) DegreeOneSmallSpectrum387.graph sourceMap0049swap=true := by decide +kernel
theorem fusedMap0049swap_checked : acceptsGraphIso
    (fused (graph core0049) (root 2) 5 2) DegreeOneSmallSpectrum369.graph fusedMap0049swap=true := by decide +kernel
theorem certified0049swap : Certified (graph core0049) (root 2) 5 2 :=
  of_native_maps core0049 DegreeOneSmallSpectrum387.graph DegreeOneSmallSpectrum369.graph
    sourceMap0049swap fusedMap0049swap sourceMap0049swap_checked fusedMap0049swap_checked
    DegreeOneSmallComparisons.comparison0049
#print axioms sourceMap0049swap_checked
#print axioms fusedMap0049swap_checked
#print axioms certified0049swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
