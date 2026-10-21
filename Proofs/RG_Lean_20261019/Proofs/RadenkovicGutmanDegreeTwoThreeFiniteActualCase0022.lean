/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0022 : Family 6 := level6.get ⟨33,by decide⟩
def sourceMap0022 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (sourceLabel 6 0 0 v)
def fusedMap0022 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 6 0 0 v)
theorem sourceMap0022_checked : acceptsGraphIso
    (source (graph core0022) (root 6) 0 0) DegreeOneSmallSpectrum062.graph sourceMap0022=true := by decide +kernel
theorem fusedMap0022_checked : acceptsGraphIso
    (fused (graph core0022) (root 6) 0 0) DegreeOneSmallSpectrum061.graph fusedMap0022=true := by decide +kernel
theorem certified0022 : Certified (graph core0022) (root 6) 0 0 :=
  of_native_maps core0022 DegreeOneSmallSpectrum062.graph DegreeOneSmallSpectrum061.graph
    sourceMap0022 fusedMap0022 sourceMap0022_checked fusedMap0022_checked
    DegreeTwoThreeFiniteComparisons.comparison0022
#print axioms sourceMap0022_checked
#print axioms fusedMap0022_checked
#print axioms certified0022
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
