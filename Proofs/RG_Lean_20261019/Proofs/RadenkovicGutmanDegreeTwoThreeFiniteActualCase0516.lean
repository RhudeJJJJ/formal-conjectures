/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0516 : Family 10 := level10.get ⟨449,by decide⟩
def sourceMap0516 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,6,7,8,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0516 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0516_checked : acceptsGraphIso
    (source (graph core0516) (root 10) 0 0) DegreeOneSmallSpectrum1045.graph sourceMap0516=true := by decide +kernel
theorem fusedMap0516_checked : acceptsGraphIso
    (fused (graph core0516) (root 10) 0 0) DegreeOneSmallSpectrum1455.graph fusedMap0516=true := by decide +kernel
theorem certified0516 : Certified (graph core0516) (root 10) 0 0 :=
  of_native_maps core0516 DegreeOneSmallSpectrum1045.graph DegreeOneSmallSpectrum1455.graph
    sourceMap0516 fusedMap0516 sourceMap0516_checked fusedMap0516_checked
    DegreeTwoThreeFiniteComparisons.comparison0516
#print axioms sourceMap0516_checked
#print axioms fusedMap0516_checked
#print axioms certified0516
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
