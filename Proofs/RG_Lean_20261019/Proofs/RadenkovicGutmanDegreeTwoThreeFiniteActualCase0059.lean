/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0059 : Family 7 := level7.get ⟨91,by decide⟩
def sourceMap0059 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,6,7,8,9,1,2,3,4,5] (sourceLabel 7 0 0 v)
def fusedMap0059 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,6,7,8,9,1,2,3,4,5] (fusedLabel 7 0 0 v)
theorem sourceMap0059_checked : acceptsGraphIso
    (source (graph core0059) (root 7) 0 0) DegreeOneSmallSpectrum114.graph sourceMap0059=true := by decide +kernel
theorem fusedMap0059_checked : acceptsGraphIso
    (fused (graph core0059) (root 7) 0 0) DegreeOneSmallSpectrum110.graph fusedMap0059=true := by decide +kernel
theorem certified0059 : Certified (graph core0059) (root 7) 0 0 :=
  of_native_maps core0059 DegreeOneSmallSpectrum114.graph DegreeOneSmallSpectrum110.graph
    sourceMap0059 fusedMap0059 sourceMap0059_checked fusedMap0059_checked
    DegreeTwoThreeFiniteComparisons.comparison0059
#print axioms sourceMap0059_checked
#print axioms fusedMap0059_checked
#print axioms certified0059
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
