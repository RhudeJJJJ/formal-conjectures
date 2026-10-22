/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0478 : Family 10 := level10.get ⟨328,by decide⟩
def sourceMap0478 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0478 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0478_checked : acceptsGraphIso
    (source (graph core0478) (root 10) 0 0) DegreeOneSmallSpectrum1070.graph sourceMap0478=true := by decide +kernel
theorem fusedMap0478_checked : acceptsGraphIso
    (fused (graph core0478) (root 10) 0 0) DegreeOneSmallSpectrum1410.graph fusedMap0478=true := by decide +kernel
theorem certified0478 : Certified (graph core0478) (root 10) 0 0 :=
  of_native_maps core0478 DegreeOneSmallSpectrum1070.graph DegreeOneSmallSpectrum1410.graph
    sourceMap0478 fusedMap0478 sourceMap0478_checked fusedMap0478_checked
    DegreeTwoThreeFiniteComparisons.comparison0478
#print axioms sourceMap0478_checked
#print axioms fusedMap0478_checked
#print axioms certified0478
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
