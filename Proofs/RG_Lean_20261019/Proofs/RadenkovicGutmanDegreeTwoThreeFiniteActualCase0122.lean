/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0122 : Family 8 := level8.get ⟨179,by decide⟩
def sourceMap0122 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap0122 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0122_checked : acceptsGraphIso
    (source (graph core0122) (root 8) 0 0) DegreeOneSmallSpectrum229.graph sourceMap0122=true := by decide +kernel
theorem fusedMap0122_checked : acceptsGraphIso
    (fused (graph core0122) (root 8) 0 0) DegreeOneSmallSpectrum228.graph fusedMap0122=true := by decide +kernel
theorem certified0122 : Certified (graph core0122) (root 8) 0 0 :=
  of_native_maps core0122 DegreeOneSmallSpectrum229.graph DegreeOneSmallSpectrum228.graph
    sourceMap0122 fusedMap0122 sourceMap0122_checked fusedMap0122_checked
    DegreeTwoThreeFiniteComparisons.comparison0122
#print axioms sourceMap0122_checked
#print axioms fusedMap0122_checked
#print axioms certified0122
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
