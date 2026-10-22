/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0951 : Family 10 := level10.get ⟨1580,by decide⟩
def sourceMap0951 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0951 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0951_checked : acceptsGraphIso
    (source (graph core0951) (root 10) 0 0) DegreeOneSmallSpectrum1631.graph sourceMap0951=true := by decide +kernel
theorem fusedMap0951_checked : acceptsGraphIso
    (fused (graph core0951) (root 10) 0 0) DegreeOneSmallSpectrum1630.graph fusedMap0951=true := by decide +kernel
theorem certified0951 : Certified (graph core0951) (root 10) 0 0 :=
  of_native_maps core0951 DegreeOneSmallSpectrum1631.graph DegreeOneSmallSpectrum1630.graph
    sourceMap0951 fusedMap0951 sourceMap0951_checked fusedMap0951_checked
    DegreeTwoThreeFiniteComparisons.comparison0951
#print axioms sourceMap0951_checked
#print axioms fusedMap0951_checked
#print axioms certified0951
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
