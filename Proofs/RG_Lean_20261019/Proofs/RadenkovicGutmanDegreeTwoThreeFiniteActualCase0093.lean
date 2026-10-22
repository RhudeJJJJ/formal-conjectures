/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0093 : Family 8 := level8.get ⟨106,by decide⟩
def sourceMap0093 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap0093 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0093_checked : acceptsGraphIso
    (source (graph core0093) (root 8) 0 0) DegreeTwoThreeSpectrum244.graph sourceMap0093=true := by decide +kernel
theorem fusedMap0093_checked : acceptsGraphIso
    (fused (graph core0093) (root 8) 0 0) DegreeOneSmallSpectrum263.graph fusedMap0093=true := by decide +kernel
theorem certified0093 : Certified (graph core0093) (root 8) 0 0 :=
  of_native_maps core0093 DegreeTwoThreeSpectrum244.graph DegreeOneSmallSpectrum263.graph
    sourceMap0093 fusedMap0093 sourceMap0093_checked fusedMap0093_checked
    DegreeTwoThreeFiniteComparisons.comparison0093
#print axioms sourceMap0093_checked
#print axioms fusedMap0093_checked
#print axioms certified0093
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
