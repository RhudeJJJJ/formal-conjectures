/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0591 : Family 7 := level7.get ⟨32,by decide⟩
def sourceMap0591 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,5,6,7,8,9,4,2,3] (sourceLabel 7 0 0 v)
def fusedMap0591 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,9,7,8] (fusedLabel 7 0 0 v)
theorem sourceMap0591_checked : acceptsGraphIso
    (source (graph core0591) (root 7) 0 0) DegreeOneSmallSpectrum116.graph sourceMap0591=true := by decide +kernel
theorem fusedMap0591_checked : acceptsGraphIso
    (fused (graph core0591) (root 7) 0 0) DegreeOneSmallSpectrum121.graph fusedMap0591=true := by decide +kernel
theorem certified0591 : Certified (graph core0591) (root 7) 0 0 :=
  of_native_maps core0591 DegreeOneSmallSpectrum116.graph DegreeOneSmallSpectrum121.graph
    sourceMap0591 fusedMap0591 sourceMap0591_checked fusedMap0591_checked
    DegreeOneSmallComparisons.comparison0591
#print axioms sourceMap0591_checked
#print axioms fusedMap0591_checked
#print axioms certified0591
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
