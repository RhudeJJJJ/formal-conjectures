/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0132 : Family 8 := level8.get ⟨203,by decide⟩
def sourceMap0132 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap0132 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0132_checked : acceptsGraphIso
    (source (graph core0132) (root 8) 0 0) DegreeOneSmallSpectrum266.graph sourceMap0132=true := by decide +kernel
theorem fusedMap0132_checked : acceptsGraphIso
    (fused (graph core0132) (root 8) 0 0) DegreeOneSmallSpectrum265.graph fusedMap0132=true := by decide +kernel
theorem certified0132 : Certified (graph core0132) (root 8) 0 0 :=
  of_native_maps core0132 DegreeOneSmallSpectrum266.graph DegreeOneSmallSpectrum265.graph
    sourceMap0132 fusedMap0132 sourceMap0132_checked fusedMap0132_checked
    DegreeTwoThreeFiniteComparisons.comparison0132
#print axioms sourceMap0132_checked
#print axioms fusedMap0132_checked
#print axioms certified0132
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
