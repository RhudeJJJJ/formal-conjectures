/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0355 : Family 9 := level9.get ⟨570,by decide⟩
def sourceMap0355 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0355 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0355_checked : acceptsGraphIso
    (source (graph core0355) (root 9) 0 0) DegreeTwoThreeSpectrum714.graph sourceMap0355=true := by decide +kernel
theorem fusedMap0355_checked : acceptsGraphIso
    (fused (graph core0355) (root 9) 0 0) DegreeOneSmallSpectrum643.graph fusedMap0355=true := by decide +kernel
theorem certified0355 : Certified (graph core0355) (root 9) 0 0 :=
  of_native_maps core0355 DegreeTwoThreeSpectrum714.graph DegreeOneSmallSpectrum643.graph
    sourceMap0355 fusedMap0355 sourceMap0355_checked fusedMap0355_checked
    DegreeTwoThreeFiniteComparisons.comparison0355
#print axioms sourceMap0355_checked
#print axioms fusedMap0355_checked
#print axioms certified0355
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
