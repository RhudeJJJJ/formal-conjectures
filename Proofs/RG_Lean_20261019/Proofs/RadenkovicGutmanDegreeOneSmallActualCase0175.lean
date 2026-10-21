/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0175 : Family 5 := level5.get ⟨1,by decide⟩
def sourceMap0175 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 5 0 4 v)
def fusedMap0175 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 0 4 v)
theorem sourceMap0175_checked : acceptsGraphIso
    (source (graph core0175) (root 5) 0 4) DegreeOneSmallSpectrum373.graph sourceMap0175=true := by decide +kernel
theorem fusedMap0175_checked : acceptsGraphIso
    (fused (graph core0175) (root 5) 0 4) DegreeOneSmallSpectrum378.graph fusedMap0175=true := by decide +kernel
theorem certified0175 : Certified (graph core0175) (root 5) 0 4 :=
  of_native_maps core0175 DegreeOneSmallSpectrum373.graph DegreeOneSmallSpectrum378.graph
    sourceMap0175 fusedMap0175 sourceMap0175_checked fusedMap0175_checked
    DegreeOneSmallComparisons.comparison0175
#print axioms sourceMap0175_checked
#print axioms fusedMap0175_checked
#print axioms certified0175
def sourceMap0175swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,7,8,9,10,11,6] (sourceLabel 5 4 0 v)
def fusedMap0175swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 4 0 v)
theorem sourceMap0175swap_checked : acceptsGraphIso
    (source (graph core0175) (root 5) 4 0) DegreeOneSmallSpectrum373.graph sourceMap0175swap=true := by decide +kernel
theorem fusedMap0175swap_checked : acceptsGraphIso
    (fused (graph core0175) (root 5) 4 0) DegreeOneSmallSpectrum378.graph fusedMap0175swap=true := by decide +kernel
theorem certified0175swap : Certified (graph core0175) (root 5) 4 0 :=
  of_native_maps core0175 DegreeOneSmallSpectrum373.graph DegreeOneSmallSpectrum378.graph
    sourceMap0175swap fusedMap0175swap sourceMap0175swap_checked fusedMap0175swap_checked
    DegreeOneSmallComparisons.comparison0175
#print axioms sourceMap0175swap_checked
#print axioms fusedMap0175swap_checked
#print axioms certified0175swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
