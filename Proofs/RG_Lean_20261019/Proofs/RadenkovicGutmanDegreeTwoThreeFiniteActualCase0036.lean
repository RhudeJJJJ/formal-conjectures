/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0036 : Family 7 := level7.get ⟨37,by decide⟩
def sourceMap0036 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9] (sourceLabel 7 0 0 v)
def fusedMap0036 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0036_checked : acceptsGraphIso
    (source (graph core0036) (root 7) 0 0) DegreeOneSmallSpectrum126.graph sourceMap0036=true := by decide +kernel
theorem fusedMap0036_checked : acceptsGraphIso
    (fused (graph core0036) (root 7) 0 0) DegreeOneSmallSpectrum124.graph fusedMap0036=true := by decide +kernel
theorem certified0036 : Certified (graph core0036) (root 7) 0 0 :=
  of_native_maps core0036 DegreeOneSmallSpectrum126.graph DegreeOneSmallSpectrum124.graph
    sourceMap0036 fusedMap0036 sourceMap0036_checked fusedMap0036_checked
    DegreeTwoThreeFiniteComparisons.comparison0036
#print axioms sourceMap0036_checked
#print axioms fusedMap0036_checked
#print axioms certified0036
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
