/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0664 : Family 10 := level10.get ⟨871,by decide⟩
def sourceMap0664 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0664 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0664_checked : acceptsGraphIso
    (source (graph core0664) (root 10) 0 0) DegreeOneSmallSpectrum1488.graph sourceMap0664=true := by decide +kernel
theorem fusedMap0664_checked : acceptsGraphIso
    (fused (graph core0664) (root 10) 0 0) DegreeOneSmallSpectrum1486.graph fusedMap0664=true := by decide +kernel
theorem certified0664 : Certified (graph core0664) (root 10) 0 0 :=
  of_native_maps core0664 DegreeOneSmallSpectrum1488.graph DegreeOneSmallSpectrum1486.graph
    sourceMap0664 fusedMap0664 sourceMap0664_checked fusedMap0664_checked
    DegreeTwoThreeFiniteComparisons.comparison0664
#print axioms sourceMap0664_checked
#print axioms fusedMap0664_checked
#print axioms certified0664
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
