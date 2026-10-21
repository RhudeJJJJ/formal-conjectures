/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0288 : Family 6 := level6.get ⟨2,by decide⟩
def sourceMap0288 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 4) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,11,7,8,9,10] (sourceLabel 6 0 3 v)
def fusedMap0288 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 0 3 v)
theorem sourceMap0288_checked : acceptsGraphIso
    (source (graph core0288) (root 6) 0 3) DegreeOneSmallSpectrum385.graph sourceMap0288=true := by decide +kernel
theorem fusedMap0288_checked : acceptsGraphIso
    (fused (graph core0288) (root 6) 0 3) DegreeOneSmallSpectrum386.graph fusedMap0288=true := by decide +kernel
theorem certified0288 : Certified (graph core0288) (root 6) 0 3 :=
  of_native_maps core0288 DegreeOneSmallSpectrum385.graph DegreeOneSmallSpectrum386.graph
    sourceMap0288 fusedMap0288 sourceMap0288_checked fusedMap0288_checked
    DegreeOneSmallComparisons.comparison0288
#print axioms sourceMap0288_checked
#print axioms fusedMap0288_checked
#print axioms certified0288
def sourceMap0288swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (sourceLabel 6 3 0 v)
def fusedMap0288swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 3 0 v)
theorem sourceMap0288swap_checked : acceptsGraphIso
    (source (graph core0288) (root 6) 3 0) DegreeOneSmallSpectrum385.graph sourceMap0288swap=true := by decide +kernel
theorem fusedMap0288swap_checked : acceptsGraphIso
    (fused (graph core0288) (root 6) 3 0) DegreeOneSmallSpectrum386.graph fusedMap0288swap=true := by decide +kernel
theorem certified0288swap : Certified (graph core0288) (root 6) 3 0 :=
  of_native_maps core0288 DegreeOneSmallSpectrum385.graph DegreeOneSmallSpectrum386.graph
    sourceMap0288swap fusedMap0288swap sourceMap0288swap_checked fusedMap0288swap_checked
    DegreeOneSmallComparisons.comparison0288
#print axioms sourceMap0288swap_checked
#print axioms fusedMap0288swap_checked
#print axioms certified0288swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
