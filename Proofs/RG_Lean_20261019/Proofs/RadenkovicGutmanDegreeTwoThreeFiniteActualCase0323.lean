/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0323 : Family 9 := level9.get ⟨493,by decide⟩
def sourceMap0323 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,9,10,11,5,6,7,8,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0323 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,4,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap0323_checked : acceptsGraphIso
    (source (graph core0323) (root 9) 0 0) DegreeOneSmallSpectrum626.graph sourceMap0323=true := by decide +kernel
theorem fusedMap0323_checked : acceptsGraphIso
    (fused (graph core0323) (root 9) 0 0) DegreeOneSmallSpectrum817.graph fusedMap0323=true := by decide +kernel
theorem certified0323 : Certified (graph core0323) (root 9) 0 0 :=
  of_native_maps core0323 DegreeOneSmallSpectrum626.graph DegreeOneSmallSpectrum817.graph
    sourceMap0323 fusedMap0323 sourceMap0323_checked fusedMap0323_checked
    DegreeTwoThreeFiniteComparisons.comparison0323
#print axioms sourceMap0323_checked
#print axioms fusedMap0323_checked
#print axioms certified0323
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
