/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0042 : Family 7 := level7.get ⟨55,by decide⟩
def sourceMap0042 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,7,8,9,5,6,2,3,4] (sourceLabel 7 0 0 v)
def fusedMap0042 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,5,6,7,8,9,4,2,3] (fusedLabel 7 0 0 v)
theorem sourceMap0042_checked : acceptsGraphIso
    (source (graph core0042) (root 7) 0 0) DegreeOneSmallSpectrum098.graph sourceMap0042=true := by decide +kernel
theorem fusedMap0042_checked : acceptsGraphIso
    (fused (graph core0042) (root 7) 0 0) DegreeOneSmallSpectrum145.graph fusedMap0042=true := by decide +kernel
theorem certified0042 : Certified (graph core0042) (root 7) 0 0 :=
  of_native_maps core0042 DegreeOneSmallSpectrum098.graph DegreeOneSmallSpectrum145.graph
    sourceMap0042 fusedMap0042 sourceMap0042_checked fusedMap0042_checked
    DegreeTwoThreeFiniteComparisons.comparison0042
#print axioms sourceMap0042_checked
#print axioms fusedMap0042_checked
#print axioms certified0042
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
