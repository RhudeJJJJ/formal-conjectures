/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0527 : Family 10 := level10.get ⟨478,by decide⟩
def sourceMap0527 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,7,8,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0527 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,7,8,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0527_checked : acceptsGraphIso
    (source (graph core0527) (root 10) 0 0) DegreeOneSmallSpectrum1370.graph sourceMap0527=true := by decide +kernel
theorem fusedMap0527_checked : acceptsGraphIso
    (fused (graph core0527) (root 10) 0 0) DegreeOneSmallSpectrum1319.graph fusedMap0527=true := by decide +kernel
theorem certified0527 : Certified (graph core0527) (root 10) 0 0 :=
  of_native_maps core0527 DegreeOneSmallSpectrum1370.graph DegreeOneSmallSpectrum1319.graph
    sourceMap0527 fusedMap0527 sourceMap0527_checked fusedMap0527_checked
    DegreeTwoThreeFiniteComparisons.comparison0527
#print axioms sourceMap0527_checked
#print axioms fusedMap0527_checked
#print axioms certified0527
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
