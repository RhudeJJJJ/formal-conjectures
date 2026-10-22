/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0306 : Family 9 := level9.get ⟨452,by decide⟩
def sourceMap0306 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0306 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap0306_checked : acceptsGraphIso
    (source (graph core0306) (root 9) 0 0) DegreeTwoThreeSpectrum679.graph sourceMap0306=true := by decide +kernel
theorem fusedMap0306_checked : acceptsGraphIso
    (fused (graph core0306) (root 9) 0 0) DegreeOneSmallSpectrum791.graph fusedMap0306=true := by decide +kernel
theorem certified0306 : Certified (graph core0306) (root 9) 0 0 :=
  of_native_maps core0306 DegreeTwoThreeSpectrum679.graph DegreeOneSmallSpectrum791.graph
    sourceMap0306 fusedMap0306 sourceMap0306_checked fusedMap0306_checked
    DegreeTwoThreeFiniteComparisons.comparison0306
#print axioms sourceMap0306_checked
#print axioms fusedMap0306_checked
#print axioms certified0306
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
