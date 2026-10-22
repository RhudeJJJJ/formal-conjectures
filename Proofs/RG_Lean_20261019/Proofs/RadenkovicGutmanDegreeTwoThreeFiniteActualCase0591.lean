/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0591 : Family 10 := level10.get ⟨668,by decide⟩
def sourceMap0591 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,11,12,7,8,9,10] (sourceLabel 10 0 0 v)
def fusedMap0591 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,11,12,7,8,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0591_checked : acceptsGraphIso
    (source (graph core0591) (root 10) 0 0) DegreeOneSmallSpectrum1262.graph sourceMap0591=true := by decide +kernel
theorem fusedMap0591_checked : acceptsGraphIso
    (fused (graph core0591) (root 10) 0 0) DegreeOneSmallSpectrum1255.graph fusedMap0591=true := by decide +kernel
theorem certified0591 : Certified (graph core0591) (root 10) 0 0 :=
  of_native_maps core0591 DegreeOneSmallSpectrum1262.graph DegreeOneSmallSpectrum1255.graph
    sourceMap0591 fusedMap0591 sourceMap0591_checked fusedMap0591_checked
    DegreeTwoThreeFiniteComparisons.comparison0591
#print axioms sourceMap0591_checked
#print axioms fusedMap0591_checked
#print axioms certified0591
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
