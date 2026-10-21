/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0037 : Family 2 := level2.get ⟨0,by decide⟩
def sourceMap0037 : (Vertices 2 ⊕ Fin 1 ⊕ Fin 8) → Fin 12 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11] (sourceLabel 2 0 7 v)
def fusedMap0037 : (Vertices 2 ⊕ Fin 9) → Fin 12 :=
  fun v => ![3,4,5,2,1,0,6,7,8,9,10,11] (fusedLabel 2 0 7 v)
theorem sourceMap0037_checked : acceptsGraphIso
    (source (graph core0037) (root 2) 0 7) DegreeOneSmallSpectrum386.graph sourceMap0037=true := by decide +kernel
theorem fusedMap0037_checked : acceptsGraphIso
    (fused (graph core0037) (root 2) 0 7) DegreeOneSmallSpectrum369.graph fusedMap0037=true := by decide +kernel
theorem certified0037 : Certified (graph core0037) (root 2) 0 7 :=
  of_native_maps core0037 DegreeOneSmallSpectrum386.graph DegreeOneSmallSpectrum369.graph
    sourceMap0037 fusedMap0037 sourceMap0037_checked fusedMap0037_checked
    DegreeOneSmallComparisons.comparison0037
#print axioms sourceMap0037_checked
#print axioms fusedMap0037_checked
#print axioms certified0037
def sourceMap0037swap : (Vertices 2 ⊕ Fin 8 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,4,5,2,1,0,7,8,9,10,11,6] (sourceLabel 2 7 0 v)
def fusedMap0037swap : (Vertices 2 ⊕ Fin 9) → Fin 12 :=
  fun v => ![3,4,5,2,1,0,6,7,8,9,10,11] (fusedLabel 2 7 0 v)
theorem sourceMap0037swap_checked : acceptsGraphIso
    (source (graph core0037) (root 2) 7 0) DegreeOneSmallSpectrum386.graph sourceMap0037swap=true := by decide +kernel
theorem fusedMap0037swap_checked : acceptsGraphIso
    (fused (graph core0037) (root 2) 7 0) DegreeOneSmallSpectrum369.graph fusedMap0037swap=true := by decide +kernel
theorem certified0037swap : Certified (graph core0037) (root 2) 7 0 :=
  of_native_maps core0037 DegreeOneSmallSpectrum386.graph DegreeOneSmallSpectrum369.graph
    sourceMap0037swap fusedMap0037swap sourceMap0037swap_checked fusedMap0037swap_checked
    DegreeOneSmallComparisons.comparison0037
#print axioms sourceMap0037swap_checked
#print axioms fusedMap0037swap_checked
#print axioms certified0037swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
