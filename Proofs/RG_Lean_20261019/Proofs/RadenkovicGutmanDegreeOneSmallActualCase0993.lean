/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0993 : Family 8 := level8.get ⟨97,by decide⟩
def sourceMap0993 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0993 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0993_checked : acceptsGraphIso
    (source (graph core0993) (root 8) 0 2) DegreeOneSmallSpectrum997.graph sourceMap0993=true := by decide +kernel
theorem fusedMap0993_checked : acceptsGraphIso
    (fused (graph core0993) (root 8) 0 2) DegreeOneSmallSpectrum998.graph fusedMap0993=true := by decide +kernel
theorem certified0993 : Certified (graph core0993) (root 8) 0 2 :=
  of_native_maps core0993 DegreeOneSmallSpectrum997.graph DegreeOneSmallSpectrum998.graph
    sourceMap0993 fusedMap0993 sourceMap0993_checked fusedMap0993_checked
    DegreeOneSmallComparisons.comparison0993
#print axioms sourceMap0993_checked
#print axioms fusedMap0993_checked
#print axioms certified0993
def sourceMap0993swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0993swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0993swap_checked : acceptsGraphIso
    (source (graph core0993) (root 8) 2 0) DegreeOneSmallSpectrum997.graph sourceMap0993swap=true := by decide +kernel
theorem fusedMap0993swap_checked : acceptsGraphIso
    (fused (graph core0993) (root 8) 2 0) DegreeOneSmallSpectrum998.graph fusedMap0993swap=true := by decide +kernel
theorem certified0993swap : Certified (graph core0993) (root 8) 2 0 :=
  of_native_maps core0993 DegreeOneSmallSpectrum997.graph DegreeOneSmallSpectrum998.graph
    sourceMap0993swap fusedMap0993swap sourceMap0993swap_checked fusedMap0993swap_checked
    DegreeOneSmallComparisons.comparison0993
#print axioms sourceMap0993swap_checked
#print axioms fusedMap0993swap_checked
#print axioms certified0993swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
