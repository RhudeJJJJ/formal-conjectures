/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0412 : Family 10 := level10.get ⟨81,by decide⟩
def sourceMap0412 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,7,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0412 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,6,0,1,2,3,4,5,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0412_checked : acceptsGraphIso
    (source (graph core0412) (root 10) 0 0) DegreeOneSmallSpectrum1052.graph sourceMap0412=true := by decide +kernel
theorem fusedMap0412_checked : acceptsGraphIso
    (fused (graph core0412) (root 10) 0 0) DegreeOneSmallSpectrum899.graph fusedMap0412=true := by decide +kernel
theorem certified0412 : Certified (graph core0412) (root 10) 0 0 :=
  of_native_maps core0412 DegreeOneSmallSpectrum1052.graph DegreeOneSmallSpectrum899.graph
    sourceMap0412 fusedMap0412 sourceMap0412_checked fusedMap0412_checked
    DegreeTwoThreeFiniteComparisons.comparison0412
#print axioms sourceMap0412_checked
#print axioms fusedMap0412_checked
#print axioms certified0412
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
