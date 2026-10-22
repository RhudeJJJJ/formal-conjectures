/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0333 : Family 9 := level9.get ⟨513,by decide⟩
def sourceMap0333 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,6,7,8,9,10,11,1,2,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0333 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,6,7,8,9,10,11,1,2,3,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap0333_checked : acceptsGraphIso
    (source (graph core0333) (root 9) 0 0) DegreeOneSmallSpectrum579.graph sourceMap0333=true := by decide +kernel
theorem fusedMap0333_checked : acceptsGraphIso
    (fused (graph core0333) (root 9) 0 0) DegreeOneSmallSpectrum573.graph fusedMap0333=true := by decide +kernel
theorem certified0333 : Certified (graph core0333) (root 9) 0 0 :=
  of_native_maps core0333 DegreeOneSmallSpectrum579.graph DegreeOneSmallSpectrum573.graph
    sourceMap0333 fusedMap0333 sourceMap0333_checked fusedMap0333_checked
    DegreeTwoThreeFiniteComparisons.comparison0333
#print axioms sourceMap0333_checked
#print axioms fusedMap0333_checked
#print axioms certified0333
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
