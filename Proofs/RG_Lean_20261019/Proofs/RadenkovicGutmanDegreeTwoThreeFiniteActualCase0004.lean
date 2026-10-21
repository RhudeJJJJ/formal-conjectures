/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0004 : Family 4 := level4.get ⟨6,by decide⟩
def sourceMap0004 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 1) → Fin 7 :=
  fun v => ![0,1,2,3,4,5,6] (sourceLabel 4 0 0 v)
def fusedMap0004 : (Vertices 4 ⊕ Fin 2) → Fin 7 :=
  fun v => ![0,1,2,3,4,5,6] (fusedLabel 4 0 0 v)
theorem sourceMap0004_checked : acceptsGraphIso
    (source (graph core0004) (root 4) 0 0) DegreeTwoThreeSpectrum013.graph sourceMap0004=true := by decide +kernel
theorem fusedMap0004_checked : acceptsGraphIso
    (fused (graph core0004) (root 4) 0 0) DegreeOneSmallSpectrum015.graph fusedMap0004=true := by decide +kernel
theorem certified0004 : Certified (graph core0004) (root 4) 0 0 :=
  of_native_maps core0004 DegreeTwoThreeSpectrum013.graph DegreeOneSmallSpectrum015.graph
    sourceMap0004 fusedMap0004 sourceMap0004_checked fusedMap0004_checked
    DegreeTwoThreeFiniteComparisons.comparison0004
#print axioms sourceMap0004_checked
#print axioms fusedMap0004_checked
#print axioms certified0004
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
