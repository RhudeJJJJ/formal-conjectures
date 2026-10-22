/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0413 : Family 10 := level10.get ⟨84,by decide⟩
def sourceMap0413 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,7,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0413 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,6,0,1,2,3,4,5,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0413_checked : acceptsGraphIso
    (source (graph core0413) (root 10) 0 0) DegreeOneSmallSpectrum1030.graph sourceMap0413=true := by decide +kernel
theorem fusedMap0413_checked : acceptsGraphIso
    (fused (graph core0413) (root 10) 0 0) DegreeOneSmallSpectrum898.graph fusedMap0413=true := by decide +kernel
theorem certified0413 : Certified (graph core0413) (root 10) 0 0 :=
  of_native_maps core0413 DegreeOneSmallSpectrum1030.graph DegreeOneSmallSpectrum898.graph
    sourceMap0413 fusedMap0413 sourceMap0413_checked fusedMap0413_checked
    DegreeTwoThreeFiniteComparisons.comparison0413
#print axioms sourceMap0413_checked
#print axioms fusedMap0413_checked
#print axioms certified0413
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
