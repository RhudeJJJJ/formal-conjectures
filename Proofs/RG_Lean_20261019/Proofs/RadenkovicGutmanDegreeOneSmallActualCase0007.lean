/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0007 : Family 1 := level1.get ⟨0,by decide⟩
def sourceMap0007 : (Vertices 1 ⊕ Fin 1 ⊕ Fin 8) → Fin 11 :=
  fun v => ![3,4,5,2,1,0,6,7,8,9,10] (sourceLabel 1 0 7 v)
def fusedMap0007 : (Vertices 1 ⊕ Fin 9) → Fin 11 :=
  fun v => ![4,5,3,2,1,0,6,7,8,9,10] (fusedLabel 1 0 7 v)
theorem sourceMap0007_checked : acceptsGraphIso
    (source (graph core0007) (root 1) 0 7) DegreeOneSmallSpectrum164.graph sourceMap0007=true := by decide +kernel
theorem fusedMap0007_checked : acceptsGraphIso
    (fused (graph core0007) (root 1) 0 7) DegreeOneSmallSpectrum168.graph fusedMap0007=true := by decide +kernel
theorem certified0007 : Certified (graph core0007) (root 1) 0 7 :=
  of_native_maps core0007 DegreeOneSmallSpectrum164.graph DegreeOneSmallSpectrum168.graph
    sourceMap0007 fusedMap0007 sourceMap0007_checked fusedMap0007_checked
    DegreeOneSmallComparisons.comparison0007
#print axioms sourceMap0007_checked
#print axioms fusedMap0007_checked
#print axioms certified0007
def sourceMap0007swap : (Vertices 1 ⊕ Fin 8 ⊕ Fin 1) → Fin 11 :=
  fun v => ![3,4,2,1,0,6,7,8,9,10,5] (sourceLabel 1 7 0 v)
def fusedMap0007swap : (Vertices 1 ⊕ Fin 9) → Fin 11 :=
  fun v => ![4,5,3,2,1,0,6,7,8,9,10] (fusedLabel 1 7 0 v)
theorem sourceMap0007swap_checked : acceptsGraphIso
    (source (graph core0007) (root 1) 7 0) DegreeOneSmallSpectrum164.graph sourceMap0007swap=true := by decide +kernel
theorem fusedMap0007swap_checked : acceptsGraphIso
    (fused (graph core0007) (root 1) 7 0) DegreeOneSmallSpectrum168.graph fusedMap0007swap=true := by decide +kernel
theorem certified0007swap : Certified (graph core0007) (root 1) 7 0 :=
  of_native_maps core0007 DegreeOneSmallSpectrum164.graph DegreeOneSmallSpectrum168.graph
    sourceMap0007swap fusedMap0007swap sourceMap0007swap_checked fusedMap0007swap_checked
    DegreeOneSmallComparisons.comparison0007
#print axioms sourceMap0007swap_checked
#print axioms fusedMap0007swap_checked
#print axioms certified0007swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
