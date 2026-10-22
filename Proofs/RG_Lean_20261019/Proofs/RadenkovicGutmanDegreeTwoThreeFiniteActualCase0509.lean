/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0509 : Family 10 := level10.get ⟨424,by decide⟩
def sourceMap0509 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0509 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0509_checked : acceptsGraphIso
    (source (graph core0509) (root 10) 0 0) DegreeOneSmallSpectrum954.graph sourceMap0509=true := by decide +kernel
theorem fusedMap0509_checked : acceptsGraphIso
    (fused (graph core0509) (root 10) 0 0) DegreeOneSmallSpectrum949.graph fusedMap0509=true := by decide +kernel
theorem certified0509 : Certified (graph core0509) (root 10) 0 0 :=
  of_native_maps core0509 DegreeOneSmallSpectrum954.graph DegreeOneSmallSpectrum949.graph
    sourceMap0509 fusedMap0509 sourceMap0509_checked fusedMap0509_checked
    DegreeTwoThreeFiniteComparisons.comparison0509
#print axioms sourceMap0509_checked
#print axioms fusedMap0509_checked
#print axioms certified0509
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
