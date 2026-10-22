/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0813 : Family 10 := level10.get ⟨1243,by decide⟩
def sourceMap0813 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0813 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0813_checked : acceptsGraphIso
    (source (graph core0813) (root 10) 0 0) DegreeTwoThreeSpectrum1458.graph sourceMap0813=true := by decide +kernel
theorem fusedMap0813_checked : acceptsGraphIso
    (fused (graph core0813) (root 10) 0 0) DegreeOneSmallSpectrum1892.graph fusedMap0813=true := by decide +kernel
theorem certified0813 : Certified (graph core0813) (root 10) 0 0 :=
  of_native_maps core0813 DegreeTwoThreeSpectrum1458.graph DegreeOneSmallSpectrum1892.graph
    sourceMap0813 fusedMap0813 sourceMap0813_checked fusedMap0813_checked
    DegreeTwoThreeFiniteComparisons.comparison0813
#print axioms sourceMap0813_checked
#print axioms fusedMap0813_checked
#print axioms certified0813
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
