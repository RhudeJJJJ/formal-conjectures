/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0165 : Family 9 := level9.get ⟨37,by decide⟩
def sourceMap0165 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,8,9,10,11,7,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0165 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,5,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap0165_checked : acceptsGraphIso
    (source (graph core0165) (root 9) 0 0) DegreeOneSmallSpectrum417.graph sourceMap0165=true := by decide +kernel
theorem fusedMap0165_checked : acceptsGraphIso
    (fused (graph core0165) (root 9) 0 0) DegreeOneSmallSpectrum382.graph fusedMap0165=true := by decide +kernel
theorem certified0165 : Certified (graph core0165) (root 9) 0 0 :=
  of_native_maps core0165 DegreeOneSmallSpectrum417.graph DegreeOneSmallSpectrum382.graph
    sourceMap0165 fusedMap0165 sourceMap0165_checked fusedMap0165_checked
    DegreeTwoThreeFiniteComparisons.comparison0165
#print axioms sourceMap0165_checked
#print axioms fusedMap0165_checked
#print axioms certified0165
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
