/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0603 : Family 10 := level10.get ⟨704,by decide⟩
def sourceMap0603 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0603 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0603_checked : acceptsGraphIso
    (source (graph core0603) (root 10) 0 0) DegreeOneSmallSpectrum1685.graph sourceMap0603=true := by decide +kernel
theorem fusedMap0603_checked : acceptsGraphIso
    (fused (graph core0603) (root 10) 0 0) DegreeOneSmallSpectrum1317.graph fusedMap0603=true := by decide +kernel
theorem certified0603 : Certified (graph core0603) (root 10) 0 0 :=
  of_native_maps core0603 DegreeOneSmallSpectrum1685.graph DegreeOneSmallSpectrum1317.graph
    sourceMap0603 fusedMap0603 sourceMap0603_checked fusedMap0603_checked
    DegreeTwoThreeFiniteComparisons.comparison0603
#print axioms sourceMap0603_checked
#print axioms fusedMap0603_checked
#print axioms certified0603
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
