/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0827 : Family 8 := level8.get ⟨27,by decide⟩
def sourceMap0827 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,7,8,9,10,6,5,3,4] (sourceLabel 8 0 0 v)
def fusedMap0827 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,5,3,4] (fusedLabel 8 0 0 v)
theorem sourceMap0827_checked : acceptsGraphIso
    (source (graph core0827) (root 8) 0 0) DegreeOneSmallSpectrum178.graph sourceMap0827=true := by decide +kernel
theorem fusedMap0827_checked : acceptsGraphIso
    (fused (graph core0827) (root 8) 0 0) DegreeOneSmallSpectrum227.graph fusedMap0827=true := by decide +kernel
theorem certified0827 : Certified (graph core0827) (root 8) 0 0 :=
  of_native_maps core0827 DegreeOneSmallSpectrum178.graph DegreeOneSmallSpectrum227.graph
    sourceMap0827 fusedMap0827 sourceMap0827_checked fusedMap0827_checked
    DegreeOneSmallComparisons.comparison0827
#print axioms sourceMap0827_checked
#print axioms fusedMap0827_checked
#print axioms certified0827
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
