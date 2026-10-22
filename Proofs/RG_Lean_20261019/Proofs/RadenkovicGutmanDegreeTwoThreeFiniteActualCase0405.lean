/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0405 : Family 10 := level10.get ⟨47,by decide⟩
def sourceMap0405 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,7,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0405 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,7,6,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0405_checked : acceptsGraphIso
    (source (graph core0405) (root 10) 0 0) DegreeOneSmallSpectrum864.graph sourceMap0405=true := by decide +kernel
theorem fusedMap0405_checked : acceptsGraphIso
    (fused (graph core0405) (root 10) 0 0) DegreeOneSmallSpectrum935.graph fusedMap0405=true := by decide +kernel
theorem certified0405 : Certified (graph core0405) (root 10) 0 0 :=
  of_native_maps core0405 DegreeOneSmallSpectrum864.graph DegreeOneSmallSpectrum935.graph
    sourceMap0405 fusedMap0405 sourceMap0405_checked fusedMap0405_checked
    DegreeTwoThreeFiniteComparisons.comparison0405
#print axioms sourceMap0405_checked
#print axioms fusedMap0405_checked
#print axioms certified0405
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
