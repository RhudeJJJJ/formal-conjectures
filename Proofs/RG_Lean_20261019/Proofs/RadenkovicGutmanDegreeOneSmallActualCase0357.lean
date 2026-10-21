/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0357 : Family 6 := level6.get ⟨12,by decide⟩
def sourceMap0357 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![1,0,5,6,7,8,4,2,3] (sourceLabel 6 0 0 v)
def fusedMap0357 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![5,0,1,2,3,4,8,6,7] (fusedLabel 6 0 0 v)
theorem sourceMap0357_checked : acceptsGraphIso
    (source (graph core0357) (root 6) 0 0) DegreeOneSmallSpectrum046.graph sourceMap0357=true := by decide +kernel
theorem fusedMap0357_checked : acceptsGraphIso
    (fused (graph core0357) (root 6) 0 0) DegreeOneSmallSpectrum060.graph fusedMap0357=true := by decide +kernel
theorem certified0357 : Certified (graph core0357) (root 6) 0 0 :=
  of_native_maps core0357 DegreeOneSmallSpectrum046.graph DegreeOneSmallSpectrum060.graph
    sourceMap0357 fusedMap0357 sourceMap0357_checked fusedMap0357_checked
    DegreeOneSmallComparisons.comparison0357
#print axioms sourceMap0357_checked
#print axioms fusedMap0357_checked
#print axioms certified0357
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
