/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0413 : Family 6 := level6.get ⟨23,by decide⟩
def sourceMap0413 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,10,7,8,9] (sourceLabel 6 0 2 v)
def fusedMap0413 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap0413_checked : acceptsGraphIso
    (source (graph core0413) (root 6) 0 2) DegreeOneSmallSpectrum291.graph sourceMap0413=true := by decide +kernel
theorem fusedMap0413_checked : acceptsGraphIso
    (fused (graph core0413) (root 6) 0 2) DegreeOneSmallSpectrum177.graph fusedMap0413=true := by decide +kernel
theorem certified0413 : Certified (graph core0413) (root 6) 0 2 :=
  of_native_maps core0413 DegreeOneSmallSpectrum291.graph DegreeOneSmallSpectrum177.graph
    sourceMap0413 fusedMap0413 sourceMap0413_checked fusedMap0413_checked
    DegreeOneSmallComparisons.comparison0413
#print axioms sourceMap0413_checked
#print axioms fusedMap0413_checked
#print axioms certified0413
def sourceMap0413swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 2 0 v)
def fusedMap0413swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap0413swap_checked : acceptsGraphIso
    (source (graph core0413) (root 6) 2 0) DegreeOneSmallSpectrum291.graph sourceMap0413swap=true := by decide +kernel
theorem fusedMap0413swap_checked : acceptsGraphIso
    (fused (graph core0413) (root 6) 2 0) DegreeOneSmallSpectrum177.graph fusedMap0413swap=true := by decide +kernel
theorem certified0413swap : Certified (graph core0413) (root 6) 2 0 :=
  of_native_maps core0413 DegreeOneSmallSpectrum291.graph DegreeOneSmallSpectrum177.graph
    sourceMap0413swap fusedMap0413swap sourceMap0413swap_checked fusedMap0413swap_checked
    DegreeOneSmallComparisons.comparison0413
#print axioms sourceMap0413swap_checked
#print axioms fusedMap0413swap_checked
#print axioms certified0413swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
