/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0011 : Family 6 := level6.get ⟨5,by decide⟩
def sourceMap0011 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![2,1,0,6,7,8,3,4,5] (sourceLabel 6 0 0 v)
def fusedMap0011 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![1,0,5,6,7,8,4,2,3] (fusedLabel 6 0 0 v)
theorem sourceMap0011_checked : acceptsGraphIso
    (source (graph core0011) (root 6) 0 0) DegreeOneSmallSpectrum042.graph sourceMap0011=true := by decide +kernel
theorem fusedMap0011_checked : acceptsGraphIso
    (fused (graph core0011) (root 6) 0 0) DegreeOneSmallSpectrum035.graph fusedMap0011=true := by decide +kernel
theorem certified0011 : Certified (graph core0011) (root 6) 0 0 :=
  of_native_maps core0011 DegreeOneSmallSpectrum042.graph DegreeOneSmallSpectrum035.graph
    sourceMap0011 fusedMap0011 sourceMap0011_checked fusedMap0011_checked
    DegreeTwoThreeFiniteComparisons.comparison0011
#print axioms sourceMap0011_checked
#print axioms fusedMap0011_checked
#print axioms certified0011
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
