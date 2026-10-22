/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0183 : Family 9 := level9.get ⟨109,by decide⟩
def sourceMap0183 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0183 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,5,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap0183_checked : acceptsGraphIso
    (source (graph core0183) (root 9) 0 0) DegreeOneSmallSpectrum410.graph sourceMap0183=true := by decide +kernel
theorem fusedMap0183_checked : acceptsGraphIso
    (fused (graph core0183) (root 9) 0 0) DegreeOneSmallSpectrum549.graph fusedMap0183=true := by decide +kernel
theorem certified0183 : Certified (graph core0183) (root 9) 0 0 :=
  of_native_maps core0183 DegreeOneSmallSpectrum410.graph DegreeOneSmallSpectrum549.graph
    sourceMap0183 fusedMap0183 sourceMap0183_checked fusedMap0183_checked
    DegreeTwoThreeFiniteComparisons.comparison0183
#print axioms sourceMap0183_checked
#print axioms fusedMap0183_checked
#print axioms certified0183
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
