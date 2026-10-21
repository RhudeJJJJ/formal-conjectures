/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0165 : Family 5 := level5.get ⟨0,by decide⟩
def sourceMap0165 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,2,3,4,5] (sourceLabel 5 1 1 v)
def fusedMap0165 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,5,6,7,8,9,1,2,3,4] (fusedLabel 5 1 1 v)
theorem sourceMap0165_checked : acceptsGraphIso
    (source (graph core0165) (root 5) 1 1) DegreeOneSmallSpectrum081.graph sourceMap0165=true := by decide +kernel
theorem fusedMap0165_checked : acceptsGraphIso
    (fused (graph core0165) (root 5) 1 1) DegreeOneSmallSpectrum073.graph fusedMap0165=true := by decide +kernel
theorem certified0165 : Certified (graph core0165) (root 5) 1 1 :=
  of_native_maps core0165 DegreeOneSmallSpectrum081.graph DegreeOneSmallSpectrum073.graph
    sourceMap0165 fusedMap0165 sourceMap0165_checked fusedMap0165_checked
    DegreeOneSmallComparisons.comparison0165
#print axioms sourceMap0165_checked
#print axioms fusedMap0165_checked
#print axioms certified0165
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
