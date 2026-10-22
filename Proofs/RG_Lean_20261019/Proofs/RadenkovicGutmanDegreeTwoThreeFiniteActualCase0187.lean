/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0187 : Family 9 := level9.get ⟨122,by decide⟩
def sourceMap0187 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,7,6,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0187 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,5,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap0187_checked : acceptsGraphIso
    (source (graph core0187) (root 9) 0 0) DegreeOneSmallSpectrum407.graph sourceMap0187=true := by decide +kernel
theorem fusedMap0187_checked : acceptsGraphIso
    (fused (graph core0187) (root 9) 0 0) DegreeOneSmallSpectrum550.graph fusedMap0187=true := by decide +kernel
theorem certified0187 : Certified (graph core0187) (root 9) 0 0 :=
  of_native_maps core0187 DegreeOneSmallSpectrum407.graph DegreeOneSmallSpectrum550.graph
    sourceMap0187 fusedMap0187 sourceMap0187_checked fusedMap0187_checked
    DegreeTwoThreeFiniteComparisons.comparison0187
#print axioms sourceMap0187_checked
#print axioms fusedMap0187_checked
#print axioms certified0187
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
