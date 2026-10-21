/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0355 : Family 6 := level6.get ⟨11,by decide⟩
def sourceMap0355 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,11,12,7,8,9,10] (sourceLabel 6 1 3 v)
def fusedMap0355 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 1 3 v)
theorem sourceMap0355_checked : acceptsGraphIso
    (source (graph core0355) (root 6) 1 3) DegreeOneSmallSpectrum1392.graph sourceMap0355=true := by decide +kernel
theorem fusedMap0355_checked : acceptsGraphIso
    (fused (graph core0355) (root 6) 1 3) DegreeOneSmallSpectrum922.graph fusedMap0355=true := by decide +kernel
theorem certified0355 : Certified (graph core0355) (root 6) 1 3 :=
  of_native_maps core0355 DegreeOneSmallSpectrum1392.graph DegreeOneSmallSpectrum922.graph
    sourceMap0355 fusedMap0355 sourceMap0355_checked fusedMap0355_checked
    DegreeOneSmallComparisons.comparison0355
#print axioms sourceMap0355_checked
#print axioms fusedMap0355_checked
#print axioms certified0355
def sourceMap0355swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 3 1 v)
def fusedMap0355swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 3 1 v)
theorem sourceMap0355swap_checked : acceptsGraphIso
    (source (graph core0355) (root 6) 3 1) DegreeOneSmallSpectrum1392.graph sourceMap0355swap=true := by decide +kernel
theorem fusedMap0355swap_checked : acceptsGraphIso
    (fused (graph core0355) (root 6) 3 1) DegreeOneSmallSpectrum922.graph fusedMap0355swap=true := by decide +kernel
theorem certified0355swap : Certified (graph core0355) (root 6) 3 1 :=
  of_native_maps core0355 DegreeOneSmallSpectrum1392.graph DegreeOneSmallSpectrum922.graph
    sourceMap0355swap fusedMap0355swap sourceMap0355swap_checked fusedMap0355swap_checked
    DegreeOneSmallComparisons.comparison0355
#print axioms sourceMap0355swap_checked
#print axioms fusedMap0355swap_checked
#print axioms certified0355swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
