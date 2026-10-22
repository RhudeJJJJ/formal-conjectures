/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0091 : Family 8 := level8.get ⟨102,by decide⟩
def sourceMap0091 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap0091 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0091_checked : acceptsGraphIso
    (source (graph core0091) (root 8) 0 0) DegreeTwoThreeSpectrum229.graph sourceMap0091=true := by decide +kernel
theorem fusedMap0091_checked : acceptsGraphIso
    (fused (graph core0091) (root 8) 0 0) DegreeOneSmallSpectrum257.graph fusedMap0091=true := by decide +kernel
theorem certified0091 : Certified (graph core0091) (root 8) 0 0 :=
  of_native_maps core0091 DegreeTwoThreeSpectrum229.graph DegreeOneSmallSpectrum257.graph
    sourceMap0091 fusedMap0091 sourceMap0091_checked fusedMap0091_checked
    DegreeTwoThreeFiniteComparisons.comparison0091
#print axioms sourceMap0091_checked
#print axioms fusedMap0091_checked
#print axioms certified0091
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
