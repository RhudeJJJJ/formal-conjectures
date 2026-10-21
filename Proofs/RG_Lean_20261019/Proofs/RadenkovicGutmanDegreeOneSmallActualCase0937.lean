/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0937 : Family 8 := level8.get ⟨70,by decide⟩
def sourceMap0937 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0937 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0937_checked : acceptsGraphIso
    (source (graph core0937) (root 8) 0 2) DegreeOneSmallSpectrum1462.graph sourceMap0937=true := by decide +kernel
theorem fusedMap0937_checked : acceptsGraphIso
    (fused (graph core0937) (root 8) 0 2) DegreeOneSmallSpectrum945.graph fusedMap0937=true := by decide +kernel
theorem certified0937 : Certified (graph core0937) (root 8) 0 2 :=
  of_native_maps core0937 DegreeOneSmallSpectrum1462.graph DegreeOneSmallSpectrum945.graph
    sourceMap0937 fusedMap0937 sourceMap0937_checked fusedMap0937_checked
    DegreeOneSmallComparisons.comparison0937
#print axioms sourceMap0937_checked
#print axioms fusedMap0937_checked
#print axioms certified0937
def sourceMap0937swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0937swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0937swap_checked : acceptsGraphIso
    (source (graph core0937) (root 8) 2 0) DegreeOneSmallSpectrum1462.graph sourceMap0937swap=true := by decide +kernel
theorem fusedMap0937swap_checked : acceptsGraphIso
    (fused (graph core0937) (root 8) 2 0) DegreeOneSmallSpectrum945.graph fusedMap0937swap=true := by decide +kernel
theorem certified0937swap : Certified (graph core0937) (root 8) 2 0 :=
  of_native_maps core0937 DegreeOneSmallSpectrum1462.graph DegreeOneSmallSpectrum945.graph
    sourceMap0937swap fusedMap0937swap sourceMap0937swap_checked fusedMap0937swap_checked
    DegreeOneSmallComparisons.comparison0937
#print axioms sourceMap0937swap_checked
#print axioms fusedMap0937swap_checked
#print axioms certified0937swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
