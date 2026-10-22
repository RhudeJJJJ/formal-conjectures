/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0309 : Family 9 := level9.get ⟨460,by decide⟩
def sourceMap0309 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0309 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,4,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap0309_checked : acceptsGraphIso
    (source (graph core0309) (root 9) 0 0) DegreeOneSmallSpectrum817.graph sourceMap0309=true := by decide +kernel
theorem fusedMap0309_checked : acceptsGraphIso
    (fused (graph core0309) (root 9) 0 0) DegreeOneSmallSpectrum812.graph fusedMap0309=true := by decide +kernel
theorem certified0309 : Certified (graph core0309) (root 9) 0 0 :=
  of_native_maps core0309 DegreeOneSmallSpectrum817.graph DegreeOneSmallSpectrum812.graph
    sourceMap0309 fusedMap0309 sourceMap0309_checked fusedMap0309_checked
    DegreeTwoThreeFiniteComparisons.comparison0309
#print axioms sourceMap0309_checked
#print axioms fusedMap0309_checked
#print axioms certified0309
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
