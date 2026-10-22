/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0181 : Family 9 := level9.get ⟨102,by decide⟩
def sourceMap0181 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0181 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap0181_checked : acceptsGraphIso
    (source (graph core0181) (root 9) 0 0) DegreeOneSmallSpectrum425.graph sourceMap0181=true := by decide +kernel
theorem fusedMap0181_checked : acceptsGraphIso
    (fused (graph core0181) (root 9) 0 0) DegreeOneSmallSpectrum557.graph fusedMap0181=true := by decide +kernel
theorem certified0181 : Certified (graph core0181) (root 9) 0 0 :=
  of_native_maps core0181 DegreeOneSmallSpectrum425.graph DegreeOneSmallSpectrum557.graph
    sourceMap0181 fusedMap0181 sourceMap0181_checked fusedMap0181_checked
    DegreeTwoThreeFiniteComparisons.comparison0181
#print axioms sourceMap0181_checked
#print axioms fusedMap0181_checked
#print axioms certified0181
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
