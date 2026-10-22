/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0284 : Family 9 := level9.get ⟨399,by decide⟩
def sourceMap0284 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,5,6,7,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0284 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,9,10,11,8,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap0284_checked : acceptsGraphIso
    (source (graph core0284) (root 9) 0 0) DegreeOneSmallSpectrum642.graph sourceMap0284=true := by decide +kernel
theorem fusedMap0284_checked : acceptsGraphIso
    (fused (graph core0284) (root 9) 0 0) DegreeOneSmallSpectrum764.graph fusedMap0284=true := by decide +kernel
theorem certified0284 : Certified (graph core0284) (root 9) 0 0 :=
  of_native_maps core0284 DegreeOneSmallSpectrum642.graph DegreeOneSmallSpectrum764.graph
    sourceMap0284 fusedMap0284 sourceMap0284_checked fusedMap0284_checked
    DegreeTwoThreeFiniteComparisons.comparison0284
#print axioms sourceMap0284_checked
#print axioms fusedMap0284_checked
#print axioms certified0284
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
