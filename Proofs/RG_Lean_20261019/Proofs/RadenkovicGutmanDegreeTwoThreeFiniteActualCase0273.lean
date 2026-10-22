/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0273 : Family 9 := level9.get ⟨371,by decide⟩
def sourceMap0273 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,5,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0273 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,10,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap0273_checked : acceptsGraphIso
    (source (graph core0273) (root 9) 0 0) DegreeOneSmallSpectrum651.graph sourceMap0273=true := by decide +kernel
theorem fusedMap0273_checked : acceptsGraphIso
    (fused (graph core0273) (root 9) 0 0) DegreeOneSmallSpectrum726.graph fusedMap0273=true := by decide +kernel
theorem certified0273 : Certified (graph core0273) (root 9) 0 0 :=
  of_native_maps core0273 DegreeOneSmallSpectrum651.graph DegreeOneSmallSpectrum726.graph
    sourceMap0273 fusedMap0273 sourceMap0273_checked fusedMap0273_checked
    DegreeTwoThreeFiniteComparisons.comparison0273
#print axioms sourceMap0273_checked
#print axioms fusedMap0273_checked
#print axioms certified0273
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
