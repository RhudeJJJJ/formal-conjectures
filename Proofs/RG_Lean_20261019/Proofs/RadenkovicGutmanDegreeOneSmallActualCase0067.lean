/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0067 : Family 3 := level3.get ⟨0,by decide⟩
def sourceMap0067 : (Vertices 3 ⊕ Fin 2 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (sourceLabel 3 1 5 v)
def fusedMap0067 : (Vertices 3 ⊕ Fin 8) → Fin 12 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9,10,11] (fusedLabel 3 1 5 v)
theorem sourceMap0067_checked : acceptsGraphIso
    (source (graph core0067) (root 3) 1 5) DegreeOneSmallSpectrum387.graph sourceMap0067=true := by decide +kernel
theorem fusedMap0067_checked : acceptsGraphIso
    (fused (graph core0067) (root 3) 1 5) DegreeOneSmallSpectrum369.graph fusedMap0067=true := by decide +kernel
theorem certified0067 : Certified (graph core0067) (root 3) 1 5 :=
  of_native_maps core0067 DegreeOneSmallSpectrum387.graph DegreeOneSmallSpectrum369.graph
    sourceMap0067 fusedMap0067 sourceMap0067_checked fusedMap0067_checked
    DegreeOneSmallComparisons.comparison0067
#print axioms sourceMap0067_checked
#print axioms fusedMap0067_checked
#print axioms certified0067
def sourceMap0067swap : (Vertices 3 ⊕ Fin 6 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,2,3,4,0,7,8,9,10,11,5,6] (sourceLabel 3 5 1 v)
def fusedMap0067swap : (Vertices 3 ⊕ Fin 8) → Fin 12 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9,10,11] (fusedLabel 3 5 1 v)
theorem sourceMap0067swap_checked : acceptsGraphIso
    (source (graph core0067) (root 3) 5 1) DegreeOneSmallSpectrum387.graph sourceMap0067swap=true := by decide +kernel
theorem fusedMap0067swap_checked : acceptsGraphIso
    (fused (graph core0067) (root 3) 5 1) DegreeOneSmallSpectrum369.graph fusedMap0067swap=true := by decide +kernel
theorem certified0067swap : Certified (graph core0067) (root 3) 5 1 :=
  of_native_maps core0067 DegreeOneSmallSpectrum387.graph DegreeOneSmallSpectrum369.graph
    sourceMap0067swap fusedMap0067swap sourceMap0067swap_checked fusedMap0067swap_checked
    DegreeOneSmallComparisons.comparison0067
#print axioms sourceMap0067swap_checked
#print axioms fusedMap0067swap_checked
#print axioms certified0067swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
