/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0716 : Family 10 := level10.get ⟨998,by decide⟩
def sourceMap0716 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0716 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0716_checked : acceptsGraphIso
    (source (graph core0716) (root 10) 0 0) DegreeTwoThreeSpectrum1284.graph sourceMap0716=true := by decide +kernel
theorem fusedMap0716_checked : acceptsGraphIso
    (fused (graph core0716) (root 10) 0 0) DegreeOneSmallSpectrum1530.graph fusedMap0716=true := by decide +kernel
theorem certified0716 : Certified (graph core0716) (root 10) 0 0 :=
  of_native_maps core0716 DegreeTwoThreeSpectrum1284.graph DegreeOneSmallSpectrum1530.graph
    sourceMap0716 fusedMap0716 sourceMap0716_checked fusedMap0716_checked
    DegreeTwoThreeFiniteComparisons.comparison0716
#print axioms sourceMap0716_checked
#print axioms fusedMap0716_checked
#print axioms certified0716
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
