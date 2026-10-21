/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0420 : Family 6 := level6.get ⟨27,by decide⟩
def sourceMap0420 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![1,0,4,5,6,7,8,2,3] (sourceLabel 6 0 0 v)
def fusedMap0420 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![6,0,1,2,3,4,5,7,8] (fusedLabel 6 0 0 v)
theorem sourceMap0420_checked : acceptsGraphIso
    (source (graph core0420) (root 6) 0 0) DegreeOneSmallSpectrum071.graph sourceMap0420=true := by decide +kernel
theorem fusedMap0420_checked : acceptsGraphIso
    (fused (graph core0420) (root 6) 0 0) DegreeOneSmallSpectrum053.graph fusedMap0420=true := by decide +kernel
theorem certified0420 : Certified (graph core0420) (root 6) 0 0 :=
  of_native_maps core0420 DegreeOneSmallSpectrum071.graph DegreeOneSmallSpectrum053.graph
    sourceMap0420 fusedMap0420 sourceMap0420_checked fusedMap0420_checked
    DegreeOneSmallComparisons.comparison0420
#print axioms sourceMap0420_checked
#print axioms fusedMap0420_checked
#print axioms certified0420
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
