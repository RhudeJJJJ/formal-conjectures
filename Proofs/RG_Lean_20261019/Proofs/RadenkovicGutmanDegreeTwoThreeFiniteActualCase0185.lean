/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0185 : Family 9 := level9.get ⟨116,by decide⟩
def sourceMap0185 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,6,7,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0185 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap0185_checked : acceptsGraphIso
    (source (graph core0185) (root 9) 0 0) DegreeOneSmallSpectrum412.graph sourceMap0185=true := by decide +kernel
theorem fusedMap0185_checked : acceptsGraphIso
    (fused (graph core0185) (root 9) 0 0) DegreeOneSmallSpectrum559.graph fusedMap0185=true := by decide +kernel
theorem certified0185 : Certified (graph core0185) (root 9) 0 0 :=
  of_native_maps core0185 DegreeOneSmallSpectrum412.graph DegreeOneSmallSpectrum559.graph
    sourceMap0185 fusedMap0185 sourceMap0185_checked fusedMap0185_checked
    DegreeTwoThreeFiniteComparisons.comparison0185
#print axioms sourceMap0185_checked
#print axioms fusedMap0185_checked
#print axioms certified0185
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
