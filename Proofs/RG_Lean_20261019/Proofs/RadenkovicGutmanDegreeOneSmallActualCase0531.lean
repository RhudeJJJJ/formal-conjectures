/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0531 : Family 7 := level7.get ⟨17,by decide⟩
def sourceMap0531 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![2,1,0,5,6,7,8,9,3,4] (sourceLabel 7 0 0 v)
def fusedMap0531 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0531_checked : acceptsGraphIso
    (source (graph core0531) (root 7) 0 0) DegreeOneSmallSpectrum128.graph sourceMap0531=true := by decide +kernel
theorem fusedMap0531_checked : acceptsGraphIso
    (fused (graph core0531) (root 7) 0 0) DegreeOneSmallSpectrum087.graph fusedMap0531=true := by decide +kernel
theorem certified0531 : Certified (graph core0531) (root 7) 0 0 :=
  of_native_maps core0531 DegreeOneSmallSpectrum128.graph DegreeOneSmallSpectrum087.graph
    sourceMap0531 fusedMap0531 sourceMap0531_checked fusedMap0531_checked
    DegreeOneSmallComparisons.comparison0531
#print axioms sourceMap0531_checked
#print axioms fusedMap0531_checked
#print axioms certified0531
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
