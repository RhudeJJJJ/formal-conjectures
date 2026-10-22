/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0131 : Family 8 := level8.get ⟨201,by decide⟩
def sourceMap0131 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap0131 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0131_checked : acceptsGraphIso
    (source (graph core0131) (root 8) 0 0) DegreeTwoThreeSpectrum233.graph sourceMap0131=true := by decide +kernel
theorem fusedMap0131_checked : acceptsGraphIso
    (fused (graph core0131) (root 8) 0 0) DegreeOneSmallSpectrum256.graph fusedMap0131=true := by decide +kernel
theorem certified0131 : Certified (graph core0131) (root 8) 0 0 :=
  of_native_maps core0131 DegreeTwoThreeSpectrum233.graph DegreeOneSmallSpectrum256.graph
    sourceMap0131 fusedMap0131 sourceMap0131_checked fusedMap0131_checked
    DegreeTwoThreeFiniteComparisons.comparison0131
#print axioms sourceMap0131_checked
#print axioms fusedMap0131_checked
#print axioms certified0131
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
