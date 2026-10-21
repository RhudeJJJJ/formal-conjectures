/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0193 : Family 5 := level5.get ⟨2,by decide⟩
def sourceMap0193 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 3) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9,10,11] (sourceLabel 5 2 2 v)
def fusedMap0193 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 2 2 v)
theorem sourceMap0193_checked : acceptsGraphIso
    (source (graph core0193) (root 5) 2 2) DegreeOneSmallSpectrum552.graph sourceMap0193=true := by decide +kernel
theorem fusedMap0193_checked : acceptsGraphIso
    (fused (graph core0193) (root 5) 2 2) DegreeOneSmallSpectrum386.graph fusedMap0193=true := by decide +kernel
theorem certified0193 : Certified (graph core0193) (root 5) 2 2 :=
  of_native_maps core0193 DegreeOneSmallSpectrum552.graph DegreeOneSmallSpectrum386.graph
    sourceMap0193 fusedMap0193 sourceMap0193_checked fusedMap0193_checked
    DegreeOneSmallComparisons.comparison0193
#print axioms sourceMap0193_checked
#print axioms fusedMap0193_checked
#print axioms certified0193
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
