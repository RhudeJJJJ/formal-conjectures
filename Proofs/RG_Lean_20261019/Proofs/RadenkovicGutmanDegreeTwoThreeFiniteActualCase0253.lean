/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0253 : Family 9 := level9.get ⟨310,by decide⟩
def sourceMap0253 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,2,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap0253 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,2,3,4,5,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap0253_checked : acceptsGraphIso
    (source (graph core0253) (root 9) 0 0) DegreeOneSmallSpectrum544.graph sourceMap0253=true := by decide +kernel
theorem fusedMap0253_checked : acceptsGraphIso
    (fused (graph core0253) (root 9) 0 0) DegreeOneSmallSpectrum540.graph fusedMap0253=true := by decide +kernel
theorem certified0253 : Certified (graph core0253) (root 9) 0 0 :=
  of_native_maps core0253 DegreeOneSmallSpectrum544.graph DegreeOneSmallSpectrum540.graph
    sourceMap0253 fusedMap0253 sourceMap0253_checked fusedMap0253_checked
    DegreeTwoThreeFiniteComparisons.comparison0253
#print axioms sourceMap0253_checked
#print axioms fusedMap0253_checked
#print axioms certified0253
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
