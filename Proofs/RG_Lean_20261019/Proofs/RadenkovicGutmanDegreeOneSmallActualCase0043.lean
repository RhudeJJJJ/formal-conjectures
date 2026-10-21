/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0043 : Family 2 := level2.get ⟨0,by decide⟩
def sourceMap0043 : (Vertices 2 ⊕ Fin 2 ⊕ Fin 6) → Fin 11 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10] (sourceLabel 2 1 5 v)
def fusedMap0043 : (Vertices 2 ⊕ Fin 8) → Fin 11 :=
  fun v => ![3,4,5,2,1,0,6,7,8,9,10] (fusedLabel 2 1 5 v)
theorem sourceMap0043_checked : acceptsGraphIso
    (source (graph core0043) (root 2) 1 5) DegreeOneSmallSpectrum202.graph sourceMap0043=true := by decide +kernel
theorem fusedMap0043_checked : acceptsGraphIso
    (fused (graph core0043) (root 2) 1 5) DegreeOneSmallSpectrum168.graph fusedMap0043=true := by decide +kernel
theorem certified0043 : Certified (graph core0043) (root 2) 1 5 :=
  of_native_maps core0043 DegreeOneSmallSpectrum202.graph DegreeOneSmallSpectrum168.graph
    sourceMap0043 fusedMap0043 sourceMap0043_checked fusedMap0043_checked
    DegreeOneSmallComparisons.comparison0043
#print axioms sourceMap0043_checked
#print axioms fusedMap0043_checked
#print axioms certified0043
def sourceMap0043swap : (Vertices 2 ⊕ Fin 6 ⊕ Fin 2) → Fin 11 :=
  fun v => ![2,3,4,1,0,7,8,9,10,5,6] (sourceLabel 2 5 1 v)
def fusedMap0043swap : (Vertices 2 ⊕ Fin 8) → Fin 11 :=
  fun v => ![3,4,5,2,1,0,6,7,8,9,10] (fusedLabel 2 5 1 v)
theorem sourceMap0043swap_checked : acceptsGraphIso
    (source (graph core0043) (root 2) 5 1) DegreeOneSmallSpectrum202.graph sourceMap0043swap=true := by decide +kernel
theorem fusedMap0043swap_checked : acceptsGraphIso
    (fused (graph core0043) (root 2) 5 1) DegreeOneSmallSpectrum168.graph fusedMap0043swap=true := by decide +kernel
theorem certified0043swap : Certified (graph core0043) (root 2) 5 1 :=
  of_native_maps core0043 DegreeOneSmallSpectrum202.graph DegreeOneSmallSpectrum168.graph
    sourceMap0043swap fusedMap0043swap sourceMap0043swap_checked fusedMap0043swap_checked
    DegreeOneSmallComparisons.comparison0043
#print axioms sourceMap0043swap_checked
#print axioms fusedMap0043swap_checked
#print axioms certified0043swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
