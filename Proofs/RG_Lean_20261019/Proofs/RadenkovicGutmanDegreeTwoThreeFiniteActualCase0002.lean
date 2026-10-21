/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0002 : Family 4 := level4.get ⟨3,by decide⟩
def sourceMap0002 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 1) → Fin 7 :=
  fun v => ![1,0,5,6,2,3,4] (sourceLabel 4 0 0 v)
def fusedMap0002 : (Vertices 4 ⊕ Fin 2) → Fin 7 :=
  fun v => ![0,4,5,6,3,1,2] (fusedLabel 4 0 0 v)
theorem sourceMap0002_checked : acceptsGraphIso
    (source (graph core0002) (root 4) 0 0) DegreeOneSmallSpectrum012.graph sourceMap0002=true := by decide +kernel
theorem fusedMap0002_checked : acceptsGraphIso
    (fused (graph core0002) (root 4) 0 0) DegreeOneSmallSpectrum009.graph fusedMap0002=true := by decide +kernel
theorem certified0002 : Certified (graph core0002) (root 4) 0 0 :=
  of_native_maps core0002 DegreeOneSmallSpectrum012.graph DegreeOneSmallSpectrum009.graph
    sourceMap0002 fusedMap0002 sourceMap0002_checked fusedMap0002_checked
    DegreeTwoThreeFiniteComparisons.comparison0002
#print axioms sourceMap0002_checked
#print axioms fusedMap0002_checked
#print axioms certified0002
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
