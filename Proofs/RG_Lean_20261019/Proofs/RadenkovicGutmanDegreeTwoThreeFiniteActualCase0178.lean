/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0178 : Family 9 := level9.get ⟨90,by decide⟩
def sourceMap0178 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0178 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,5,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap0178_checked : acceptsGraphIso
    (source (graph core0178) (root 9) 0 0) DegreeOneSmallSpectrum409.graph sourceMap0178=true := by decide +kernel
theorem fusedMap0178_checked : acceptsGraphIso
    (fused (graph core0178) (root 9) 0 0) DegreeOneSmallSpectrum546.graph fusedMap0178=true := by decide +kernel
theorem certified0178 : Certified (graph core0178) (root 9) 0 0 :=
  of_native_maps core0178 DegreeOneSmallSpectrum409.graph DegreeOneSmallSpectrum546.graph
    sourceMap0178 fusedMap0178 sourceMap0178_checked fusedMap0178_checked
    DegreeTwoThreeFiniteComparisons.comparison0178
#print axioms sourceMap0178_checked
#print axioms fusedMap0178_checked
#print axioms certified0178
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
