/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0488 : Family 10 := level10.get ⟨360,by decide⟩
def sourceMap0488 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0488 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0488_checked : acceptsGraphIso
    (source (graph core0488) (root 10) 0 0) DegreeOneSmallSpectrum1019.graph sourceMap0488=true := by decide +kernel
theorem fusedMap0488_checked : acceptsGraphIso
    (fused (graph core0488) (root 10) 0 0) DegreeOneSmallSpectrum1420.graph fusedMap0488=true := by decide +kernel
theorem certified0488 : Certified (graph core0488) (root 10) 0 0 :=
  of_native_maps core0488 DegreeOneSmallSpectrum1019.graph DegreeOneSmallSpectrum1420.graph
    sourceMap0488 fusedMap0488 sourceMap0488_checked fusedMap0488_checked
    DegreeTwoThreeFiniteComparisons.comparison0488
#print axioms sourceMap0488_checked
#print axioms fusedMap0488_checked
#print axioms certified0488
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
