/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0124 : Family 8 := level8.get ⟨181,by decide⟩
def sourceMap0124 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,7,8,9,10,1,2,3,4,5,6] (sourceLabel 8 0 0 v)
def fusedMap0124 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,7,8,9,10,1,2,3,4,5,6] (fusedLabel 8 0 0 v)
theorem sourceMap0124_checked : acceptsGraphIso
    (source (graph core0124) (root 8) 0 0) DegreeOneSmallSpectrum209.graph sourceMap0124=true := by decide +kernel
theorem fusedMap0124_checked : acceptsGraphIso
    (fused (graph core0124) (root 8) 0 0) DegreeOneSmallSpectrum208.graph fusedMap0124=true := by decide +kernel
theorem certified0124 : Certified (graph core0124) (root 8) 0 0 :=
  of_native_maps core0124 DegreeOneSmallSpectrum209.graph DegreeOneSmallSpectrum208.graph
    sourceMap0124 fusedMap0124 sourceMap0124_checked fusedMap0124_checked
    DegreeTwoThreeFiniteComparisons.comparison0124
#print axioms sourceMap0124_checked
#print axioms fusedMap0124_checked
#print axioms certified0124
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
