/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0720 : Family 7 := level7.get ⟨82,by decide⟩
def sourceMap0720 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 0 3 v)
def fusedMap0720 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0720_checked : acceptsGraphIso
    (source (graph core0720) (root 7) 0 3) DegreeOneSmallSpectrum1298.graph sourceMap0720=true := by decide +kernel
theorem fusedMap0720_checked : acceptsGraphIso
    (fused (graph core0720) (root 7) 0 3) DegreeOneSmallSpectrum1301.graph fusedMap0720=true := by decide +kernel
theorem certified0720 : Certified (graph core0720) (root 7) 0 3 :=
  of_native_maps core0720 DegreeOneSmallSpectrum1298.graph DegreeOneSmallSpectrum1301.graph
    sourceMap0720 fusedMap0720 sourceMap0720_checked fusedMap0720_checked
    DegreeOneSmallComparisons.comparison0720
#print axioms sourceMap0720_checked
#print axioms fusedMap0720_checked
#print axioms certified0720
def sourceMap0720swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,12,8] (sourceLabel 7 3 0 v)
def fusedMap0720swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0720swap_checked : acceptsGraphIso
    (source (graph core0720) (root 7) 3 0) DegreeOneSmallSpectrum1298.graph sourceMap0720swap=true := by decide +kernel
theorem fusedMap0720swap_checked : acceptsGraphIso
    (fused (graph core0720) (root 7) 3 0) DegreeOneSmallSpectrum1301.graph fusedMap0720swap=true := by decide +kernel
theorem certified0720swap : Certified (graph core0720) (root 7) 3 0 :=
  of_native_maps core0720 DegreeOneSmallSpectrum1298.graph DegreeOneSmallSpectrum1301.graph
    sourceMap0720swap fusedMap0720swap sourceMap0720swap_checked fusedMap0720swap_checked
    DegreeOneSmallComparisons.comparison0720
#print axioms sourceMap0720swap_checked
#print axioms fusedMap0720swap_checked
#print axioms certified0720swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
