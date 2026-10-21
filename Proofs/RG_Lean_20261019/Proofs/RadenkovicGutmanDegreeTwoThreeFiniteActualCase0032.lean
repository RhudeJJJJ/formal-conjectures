/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0032 : Family 7 := level7.get ⟨24,by decide⟩
def sourceMap0032 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,2,3,4,5] (sourceLabel 7 0 0 v)
def fusedMap0032 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,2,3,4,5] (fusedLabel 7 0 0 v)
theorem sourceMap0032_checked : acceptsGraphIso
    (source (graph core0032) (root 7) 0 0) DegreeOneSmallSpectrum082.graph sourceMap0032=true := by decide +kernel
theorem fusedMap0032_checked : acceptsGraphIso
    (fused (graph core0032) (root 7) 0 0) DegreeOneSmallSpectrum081.graph fusedMap0032=true := by decide +kernel
theorem certified0032 : Certified (graph core0032) (root 7) 0 0 :=
  of_native_maps core0032 DegreeOneSmallSpectrum082.graph DegreeOneSmallSpectrum081.graph
    sourceMap0032 fusedMap0032 sourceMap0032_checked fusedMap0032_checked
    DegreeTwoThreeFiniteComparisons.comparison0032
#print axioms sourceMap0032_checked
#print axioms fusedMap0032_checked
#print axioms certified0032
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
