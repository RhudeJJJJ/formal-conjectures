/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0913 : Family 8 := level8.get ⟨59,by decide⟩
def sourceMap0913 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,11,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap0913 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0913_checked : acceptsGraphIso
    (source (graph core0913) (root 8) 0 2) DegreeOneSmallSpectrum1391.graph sourceMap0913=true := by decide +kernel
theorem fusedMap0913_checked : acceptsGraphIso
    (fused (graph core0913) (root 8) 0 2) DegreeOneSmallSpectrum918.graph fusedMap0913=true := by decide +kernel
theorem certified0913 : Certified (graph core0913) (root 8) 0 2 :=
  of_native_maps core0913 DegreeOneSmallSpectrum1391.graph DegreeOneSmallSpectrum918.graph
    sourceMap0913 fusedMap0913 sourceMap0913_checked fusedMap0913_checked
    DegreeOneSmallComparisons.comparison0913
#print axioms sourceMap0913_checked
#print axioms fusedMap0913_checked
#print axioms certified0913
def sourceMap0913swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 8 2 0 v)
def fusedMap0913swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0913swap_checked : acceptsGraphIso
    (source (graph core0913) (root 8) 2 0) DegreeOneSmallSpectrum1391.graph sourceMap0913swap=true := by decide +kernel
theorem fusedMap0913swap_checked : acceptsGraphIso
    (fused (graph core0913) (root 8) 2 0) DegreeOneSmallSpectrum918.graph fusedMap0913swap=true := by decide +kernel
theorem certified0913swap : Certified (graph core0913) (root 8) 2 0 :=
  of_native_maps core0913 DegreeOneSmallSpectrum1391.graph DegreeOneSmallSpectrum918.graph
    sourceMap0913swap fusedMap0913swap sourceMap0913swap_checked fusedMap0913swap_checked
    DegreeOneSmallComparisons.comparison0913
#print axioms sourceMap0913swap_checked
#print axioms fusedMap0913swap_checked
#print axioms certified0913swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
