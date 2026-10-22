/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0068 : Family 8 := level8.get ⟨28,by decide⟩
def sourceMap0068 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,7,8,9,10,6,3,4,5] (sourceLabel 8 0 0 v)
def fusedMap0068 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,5,3,4] (fusedLabel 8 0 0 v)
theorem sourceMap0068_checked : acceptsGraphIso
    (source (graph core0068) (root 8) 0 0) DegreeOneSmallSpectrum171.graph sourceMap0068=true := by decide +kernel
theorem fusedMap0068_checked : acceptsGraphIso
    (fused (graph core0068) (root 8) 0 0) DegreeOneSmallSpectrum217.graph fusedMap0068=true := by decide +kernel
theorem certified0068 : Certified (graph core0068) (root 8) 0 0 :=
  of_native_maps core0068 DegreeOneSmallSpectrum171.graph DegreeOneSmallSpectrum217.graph
    sourceMap0068 fusedMap0068 sourceMap0068_checked fusedMap0068_checked
    DegreeTwoThreeFiniteComparisons.comparison0068
#print axioms sourceMap0068_checked
#print axioms fusedMap0068_checked
#print axioms certified0068
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
