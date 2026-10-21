/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0299 : Family 6 := level6.get ⟨3,by decide⟩
def sourceMap0299 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,2,3,4,5] (sourceLabel 6 1 1 v)
def fusedMap0299 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (fusedLabel 6 1 1 v)
theorem sourceMap0299_checked : acceptsGraphIso
    (source (graph core0299) (root 6) 1 1) DegreeOneSmallSpectrum201.graph sourceMap0299=true := by decide +kernel
theorem fusedMap0299_checked : acceptsGraphIso
    (fused (graph core0299) (root 6) 1 1) DegreeOneSmallSpectrum166.graph fusedMap0299=true := by decide +kernel
theorem certified0299 : Certified (graph core0299) (root 6) 1 1 :=
  of_native_maps core0299 DegreeOneSmallSpectrum201.graph DegreeOneSmallSpectrum166.graph
    sourceMap0299 fusedMap0299 sourceMap0299_checked fusedMap0299_checked
    DegreeOneSmallComparisons.comparison0299
#print axioms sourceMap0299_checked
#print axioms fusedMap0299_checked
#print axioms certified0299
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
