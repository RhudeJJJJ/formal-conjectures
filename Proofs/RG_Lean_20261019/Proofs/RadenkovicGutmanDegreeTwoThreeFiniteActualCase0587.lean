/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0587 : Family 10 := level10.get ⟨660,by decide⟩
def sourceMap0587 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,6,7,8,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0587 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,10,11,12,9,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0587_checked : acceptsGraphIso
    (source (graph core0587) (root 10) 0 0) DegreeOneSmallSpectrum1612.graph sourceMap0587=true := by decide +kernel
theorem fusedMap0587_checked : acceptsGraphIso
    (fused (graph core0587) (root 10) 0 0) DegreeOneSmallSpectrum1266.graph fusedMap0587=true := by decide +kernel
theorem certified0587 : Certified (graph core0587) (root 10) 0 0 :=
  of_native_maps core0587 DegreeOneSmallSpectrum1612.graph DegreeOneSmallSpectrum1266.graph
    sourceMap0587 fusedMap0587 sourceMap0587_checked fusedMap0587_checked
    DegreeTwoThreeFiniteComparisons.comparison0587
#print axioms sourceMap0587_checked
#print axioms fusedMap0587_checked
#print axioms certified0587
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
