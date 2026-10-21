/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0309 : Family 6 := level6.get ⟨4,by decide⟩
def sourceMap0309 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,6,2,3,4] (sourceLabel 6 1 2 v)
def fusedMap0309 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 1 2 v)
theorem sourceMap0309_checked : acceptsGraphIso
    (source (graph core0309) (root 6) 1 2) DegreeOneSmallSpectrum575.graph sourceMap0309=true := by decide +kernel
theorem fusedMap0309_checked : acceptsGraphIso
    (fused (graph core0309) (root 6) 1 2) DegreeOneSmallSpectrum396.graph fusedMap0309=true := by decide +kernel
theorem certified0309 : Certified (graph core0309) (root 6) 1 2 :=
  of_native_maps core0309 DegreeOneSmallSpectrum575.graph DegreeOneSmallSpectrum396.graph
    sourceMap0309 fusedMap0309 sourceMap0309_checked fusedMap0309_checked
    DegreeOneSmallComparisons.comparison0309
#print axioms sourceMap0309_checked
#print axioms fusedMap0309_checked
#print axioms certified0309
def sourceMap0309swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (sourceLabel 6 2 1 v)
def fusedMap0309swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 2 1 v)
theorem sourceMap0309swap_checked : acceptsGraphIso
    (source (graph core0309) (root 6) 2 1) DegreeOneSmallSpectrum575.graph sourceMap0309swap=true := by decide +kernel
theorem fusedMap0309swap_checked : acceptsGraphIso
    (fused (graph core0309) (root 6) 2 1) DegreeOneSmallSpectrum396.graph fusedMap0309swap=true := by decide +kernel
theorem certified0309swap : Certified (graph core0309) (root 6) 2 1 :=
  of_native_maps core0309 DegreeOneSmallSpectrum575.graph DegreeOneSmallSpectrum396.graph
    sourceMap0309swap fusedMap0309swap sourceMap0309swap_checked fusedMap0309swap_checked
    DegreeOneSmallComparisons.comparison0309
#print axioms sourceMap0309swap_checked
#print axioms fusedMap0309swap_checked
#print axioms certified0309swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
