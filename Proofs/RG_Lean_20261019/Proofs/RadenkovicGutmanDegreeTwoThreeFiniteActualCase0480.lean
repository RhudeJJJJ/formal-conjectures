/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0480 : Family 10 := level10.get ⟨336,by decide⟩
def sourceMap0480 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0480 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0480_checked : acceptsGraphIso
    (source (graph core0480) (root 10) 0 0) DegreeOneSmallSpectrum1054.graph sourceMap0480=true := by decide +kernel
theorem fusedMap0480_checked : acceptsGraphIso
    (fused (graph core0480) (root 10) 0 0) DegreeOneSmallSpectrum1426.graph fusedMap0480=true := by decide +kernel
theorem certified0480 : Certified (graph core0480) (root 10) 0 0 :=
  of_native_maps core0480 DegreeOneSmallSpectrum1054.graph DegreeOneSmallSpectrum1426.graph
    sourceMap0480 fusedMap0480 sourceMap0480_checked fusedMap0480_checked
    DegreeTwoThreeFiniteComparisons.comparison0480
#print axioms sourceMap0480_checked
#print axioms fusedMap0480_checked
#print axioms certified0480
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
