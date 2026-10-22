/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0393 : Family 9 := level9.get ⟨667,by decide⟩
def sourceMap0393 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,8,9,10,11,1,2,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap0393 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,8,9,10,11,1,2,3,4,5,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap0393_checked : acceptsGraphIso
    (source (graph core0393) (root 9) 0 0) DegreeOneSmallSpectrum611.graph sourceMap0393=true := by decide +kernel
theorem fusedMap0393_checked : acceptsGraphIso
    (fused (graph core0393) (root 9) 0 0) DegreeOneSmallSpectrum607.graph fusedMap0393=true := by decide +kernel
theorem certified0393 : Certified (graph core0393) (root 9) 0 0 :=
  of_native_maps core0393 DegreeOneSmallSpectrum611.graph DegreeOneSmallSpectrum607.graph
    sourceMap0393 fusedMap0393 sourceMap0393_checked fusedMap0393_checked
    DegreeTwoThreeFiniteComparisons.comparison0393
#print axioms sourceMap0393_checked
#print axioms fusedMap0393_checked
#print axioms certified0393
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
