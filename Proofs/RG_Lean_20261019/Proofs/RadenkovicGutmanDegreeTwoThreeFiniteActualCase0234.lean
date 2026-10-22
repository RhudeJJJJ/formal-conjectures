/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0234 : Family 9 := level9.get ⟨265,by decide⟩
def sourceMap0234 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0234 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap0234_checked : acceptsGraphIso
    (source (graph core0234) (root 9) 0 0) DegreeOneSmallSpectrum531.graph sourceMap0234=true := by decide +kernel
theorem fusedMap0234_checked : acceptsGraphIso
    (fused (graph core0234) (root 9) 0 0) DegreeOneSmallSpectrum515.graph fusedMap0234=true := by decide +kernel
theorem certified0234 : Certified (graph core0234) (root 9) 0 0 :=
  of_native_maps core0234 DegreeOneSmallSpectrum531.graph DegreeOneSmallSpectrum515.graph
    sourceMap0234 fusedMap0234 sourceMap0234_checked fusedMap0234_checked
    DegreeTwoThreeFiniteComparisons.comparison0234
#print axioms sourceMap0234_checked
#print axioms fusedMap0234_checked
#print axioms certified0234
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
