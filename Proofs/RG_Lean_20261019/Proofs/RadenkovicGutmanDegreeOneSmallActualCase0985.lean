/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0985 : Family 8 := level8.get ⟨95,by decide⟩
def sourceMap0985 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0985 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0985_checked : acceptsGraphIso
    (source (graph core0985) (root 8) 0 2) DegreeOneSmallSpectrum984.graph sourceMap0985=true := by decide +kernel
theorem fusedMap0985_checked : acceptsGraphIso
    (fused (graph core0985) (root 8) 0 2) DegreeOneSmallSpectrum985.graph fusedMap0985=true := by decide +kernel
theorem certified0985 : Certified (graph core0985) (root 8) 0 2 :=
  of_native_maps core0985 DegreeOneSmallSpectrum984.graph DegreeOneSmallSpectrum985.graph
    sourceMap0985 fusedMap0985 sourceMap0985_checked fusedMap0985_checked
    DegreeOneSmallComparisons.comparison0985
#print axioms sourceMap0985_checked
#print axioms fusedMap0985_checked
#print axioms certified0985
def sourceMap0985swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0985swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0985swap_checked : acceptsGraphIso
    (source (graph core0985) (root 8) 2 0) DegreeOneSmallSpectrum984.graph sourceMap0985swap=true := by decide +kernel
theorem fusedMap0985swap_checked : acceptsGraphIso
    (fused (graph core0985) (root 8) 2 0) DegreeOneSmallSpectrum985.graph fusedMap0985swap=true := by decide +kernel
theorem certified0985swap : Certified (graph core0985) (root 8) 2 0 :=
  of_native_maps core0985 DegreeOneSmallSpectrum984.graph DegreeOneSmallSpectrum985.graph
    sourceMap0985swap fusedMap0985swap sourceMap0985swap_checked fusedMap0985swap_checked
    DegreeOneSmallComparisons.comparison0985
#print axioms sourceMap0985swap_checked
#print axioms fusedMap0985swap_checked
#print axioms certified0985swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
