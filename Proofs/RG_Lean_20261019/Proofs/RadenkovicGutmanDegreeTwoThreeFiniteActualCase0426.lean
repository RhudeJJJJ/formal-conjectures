/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0426 : Family 10 := level10.get ⟨142,by decide⟩
def sourceMap0426 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,7,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0426 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0426_checked : acceptsGraphIso
    (source (graph core0426) (root 10) 0 0) DegreeOneSmallSpectrum1036.graph sourceMap0426=true := by decide +kernel
theorem fusedMap0426_checked : acceptsGraphIso
    (fused (graph core0426) (root 10) 0 0) DegreeOneSmallSpectrum927.graph fusedMap0426=true := by decide +kernel
theorem certified0426 : Certified (graph core0426) (root 10) 0 0 :=
  of_native_maps core0426 DegreeOneSmallSpectrum1036.graph DegreeOneSmallSpectrum927.graph
    sourceMap0426 fusedMap0426 sourceMap0426_checked fusedMap0426_checked
    DegreeTwoThreeFiniteComparisons.comparison0426
#print axioms sourceMap0426_checked
#print axioms fusedMap0426_checked
#print axioms certified0426
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
