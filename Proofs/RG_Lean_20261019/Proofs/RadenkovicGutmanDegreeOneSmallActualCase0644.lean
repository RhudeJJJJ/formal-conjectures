/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0644 : Family 7 := level7.get ⟨46,by decide⟩
def sourceMap0644 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0644 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0644_checked : acceptsGraphIso
    (source (graph core0644) (root 7) 1 2) DegreeOneSmallSpectrum1421.graph sourceMap0644=true := by decide +kernel
theorem fusedMap0644_checked : acceptsGraphIso
    (fused (graph core0644) (root 7) 1 2) DegreeOneSmallSpectrum924.graph fusedMap0644=true := by decide +kernel
theorem certified0644 : Certified (graph core0644) (root 7) 1 2 :=
  of_native_maps core0644 DegreeOneSmallSpectrum1421.graph DegreeOneSmallSpectrum924.graph
    sourceMap0644 fusedMap0644 sourceMap0644_checked fusedMap0644_checked
    DegreeOneSmallComparisons.comparison0644
#print axioms sourceMap0644_checked
#print axioms fusedMap0644_checked
#print axioms certified0644
def sourceMap0644swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0644swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0644swap_checked : acceptsGraphIso
    (source (graph core0644) (root 7) 2 1) DegreeOneSmallSpectrum1421.graph sourceMap0644swap=true := by decide +kernel
theorem fusedMap0644swap_checked : acceptsGraphIso
    (fused (graph core0644) (root 7) 2 1) DegreeOneSmallSpectrum924.graph fusedMap0644swap=true := by decide +kernel
theorem certified0644swap : Certified (graph core0644) (root 7) 2 1 :=
  of_native_maps core0644 DegreeOneSmallSpectrum1421.graph DegreeOneSmallSpectrum924.graph
    sourceMap0644swap fusedMap0644swap sourceMap0644swap_checked fusedMap0644swap_checked
    DegreeOneSmallComparisons.comparison0644
#print axioms sourceMap0644swap_checked
#print axioms fusedMap0644swap_checked
#print axioms certified0644swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
