/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0874 : Family 10 := level10.get ⟨1382,by decide⟩
def sourceMap0874 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0874 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0874_checked : acceptsGraphIso
    (source (graph core0874) (root 10) 0 0) DegreeOneSmallSpectrum1652.graph sourceMap0874=true := by decide +kernel
theorem fusedMap0874_checked : acceptsGraphIso
    (fused (graph core0874) (root 10) 0 0) DegreeOneSmallSpectrum1635.graph fusedMap0874=true := by decide +kernel
theorem certified0874 : Certified (graph core0874) (root 10) 0 0 :=
  of_native_maps core0874 DegreeOneSmallSpectrum1652.graph DegreeOneSmallSpectrum1635.graph
    sourceMap0874 fusedMap0874 sourceMap0874_checked fusedMap0874_checked
    DegreeTwoThreeFiniteComparisons.comparison0874
#print axioms sourceMap0874_checked
#print axioms fusedMap0874_checked
#print axioms certified0874
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
