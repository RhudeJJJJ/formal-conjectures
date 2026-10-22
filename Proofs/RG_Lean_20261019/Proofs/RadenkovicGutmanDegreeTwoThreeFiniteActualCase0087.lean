/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0087 : Family 8 := level8.get ⟨89,by decide⟩
def sourceMap0087 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,6,2,3,4,5] (sourceLabel 8 0 0 v)
def fusedMap0087 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,6,2,3,4,5] (fusedLabel 8 0 0 v)
theorem sourceMap0087_checked : acceptsGraphIso
    (source (graph core0087) (root 8) 0 0) DegreeOneSmallSpectrum204.graph sourceMap0087=true := by decide +kernel
theorem fusedMap0087_checked : acceptsGraphIso
    (fused (graph core0087) (root 8) 0 0) DegreeOneSmallSpectrum199.graph fusedMap0087=true := by decide +kernel
theorem certified0087 : Certified (graph core0087) (root 8) 0 0 :=
  of_native_maps core0087 DegreeOneSmallSpectrum204.graph DegreeOneSmallSpectrum199.graph
    sourceMap0087 fusedMap0087 sourceMap0087_checked fusedMap0087_checked
    DegreeTwoThreeFiniteComparisons.comparison0087
#print axioms sourceMap0087_checked
#print axioms fusedMap0087_checked
#print axioms certified0087
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
