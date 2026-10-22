/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0299 : Family 9 := level9.get ⟨434,by decide⟩
def sourceMap0299 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0299 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0299_checked : acceptsGraphIso
    (source (graph core0299) (root 9) 0 0) DegreeOneSmallSpectrum516.graph sourceMap0299=true := by decide +kernel
theorem fusedMap0299_checked : acceptsGraphIso
    (fused (graph core0299) (root 9) 0 0) DegreeOneSmallSpectrum515.graph fusedMap0299=true := by decide +kernel
theorem certified0299 : Certified (graph core0299) (root 9) 0 0 :=
  of_native_maps core0299 DegreeOneSmallSpectrum516.graph DegreeOneSmallSpectrum515.graph
    sourceMap0299 fusedMap0299 sourceMap0299_checked fusedMap0299_checked
    DegreeTwoThreeFiniteComparisons.comparison0299
#print axioms sourceMap0299_checked
#print axioms fusedMap0299_checked
#print axioms certified0299
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
