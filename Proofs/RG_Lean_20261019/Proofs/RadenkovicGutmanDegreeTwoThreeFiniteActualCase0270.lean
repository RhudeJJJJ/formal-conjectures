/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0270 : Family 9 := level9.get ⟨363,by decide⟩
def sourceMap0270 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,5,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0270 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,10,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap0270_checked : acceptsGraphIso
    (source (graph core0270) (root 9) 0 0) DegreeOneSmallSpectrum650.graph sourceMap0270=true := by decide +kernel
theorem fusedMap0270_checked : acceptsGraphIso
    (fused (graph core0270) (root 9) 0 0) DegreeOneSmallSpectrum706.graph fusedMap0270=true := by decide +kernel
theorem certified0270 : Certified (graph core0270) (root 9) 0 0 :=
  of_native_maps core0270 DegreeOneSmallSpectrum650.graph DegreeOneSmallSpectrum706.graph
    sourceMap0270 fusedMap0270 sourceMap0270_checked fusedMap0270_checked
    DegreeTwoThreeFiniteComparisons.comparison0270
#print axioms sourceMap0270_checked
#print axioms fusedMap0270_checked
#print axioms certified0270
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
