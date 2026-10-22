/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0511 : Family 10 := level10.get ⟨433,by decide⟩
def sourceMap0511 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,6,7,8,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0511 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0511_checked : acceptsGraphIso
    (source (graph core0511) (root 10) 0 0) DegreeOneSmallSpectrum1038.graph sourceMap0511=true := by decide +kernel
theorem fusedMap0511_checked : acceptsGraphIso
    (fused (graph core0511) (root 10) 0 0) DegreeOneSmallSpectrum1452.graph fusedMap0511=true := by decide +kernel
theorem certified0511 : Certified (graph core0511) (root 10) 0 0 :=
  of_native_maps core0511 DegreeOneSmallSpectrum1038.graph DegreeOneSmallSpectrum1452.graph
    sourceMap0511 fusedMap0511 sourceMap0511_checked fusedMap0511_checked
    DegreeTwoThreeFiniteComparisons.comparison0511
#print axioms sourceMap0511_checked
#print axioms fusedMap0511_checked
#print axioms certified0511
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
