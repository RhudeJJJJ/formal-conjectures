/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0217 : Family 5 := level5.get ⟨5,by decide⟩
def sourceMap0217 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 5 2 2 v)
def fusedMap0217 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 2 2 v)
theorem sourceMap0217_checked : acceptsGraphIso
    (source (graph core0217) (root 5) 2 2) DegreeOneSmallSpectrum669.graph sourceMap0217=true := by decide +kernel
theorem fusedMap0217_checked : acceptsGraphIso
    (fused (graph core0217) (root 5) 2 2) DegreeOneSmallSpectrum370.graph fusedMap0217=true := by decide +kernel
theorem certified0217 : Certified (graph core0217) (root 5) 2 2 :=
  of_native_maps core0217 DegreeOneSmallSpectrum669.graph DegreeOneSmallSpectrum370.graph
    sourceMap0217 fusedMap0217 sourceMap0217_checked fusedMap0217_checked
    DegreeOneSmallComparisons.comparison0217
#print axioms sourceMap0217_checked
#print axioms fusedMap0217_checked
#print axioms certified0217
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
