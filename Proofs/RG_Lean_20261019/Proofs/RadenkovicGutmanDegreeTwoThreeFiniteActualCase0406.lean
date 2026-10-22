/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0406 : Family 10 := level10.get ⟨50,by decide⟩
def sourceMap0406 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,7,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0406 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,7,6,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0406_checked : acceptsGraphIso
    (source (graph core0406) (root 10) 0 0) DegreeOneSmallSpectrum863.graph sourceMap0406=true := by decide +kernel
theorem fusedMap0406_checked : acceptsGraphIso
    (fused (graph core0406) (root 10) 0 0) DegreeOneSmallSpectrum929.graph fusedMap0406=true := by decide +kernel
theorem certified0406 : Certified (graph core0406) (root 10) 0 0 :=
  of_native_maps core0406 DegreeOneSmallSpectrum863.graph DegreeOneSmallSpectrum929.graph
    sourceMap0406 fusedMap0406 sourceMap0406_checked fusedMap0406_checked
    DegreeTwoThreeFiniteComparisons.comparison0406
#print axioms sourceMap0406_checked
#print axioms fusedMap0406_checked
#print axioms certified0406
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
