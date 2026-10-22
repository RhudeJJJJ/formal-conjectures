/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0440 : Family 10 := level10.get ⟨185,by decide⟩
def sourceMap0440 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0440 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0440_checked : acceptsGraphIso
    (source (graph core0440) (root 10) 0 0) DegreeOneSmallSpectrum956.graph sourceMap0440=true := by decide +kernel
theorem fusedMap0440_checked : acceptsGraphIso
    (fused (graph core0440) (root 10) 0 0) DegreeOneSmallSpectrum951.graph fusedMap0440=true := by decide +kernel
theorem certified0440 : Certified (graph core0440) (root 10) 0 0 :=
  of_native_maps core0440 DegreeOneSmallSpectrum956.graph DegreeOneSmallSpectrum951.graph
    sourceMap0440 fusedMap0440 sourceMap0440_checked fusedMap0440_checked
    DegreeTwoThreeFiniteComparisons.comparison0440
#print axioms sourceMap0440_checked
#print axioms fusedMap0440_checked
#print axioms certified0440
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
