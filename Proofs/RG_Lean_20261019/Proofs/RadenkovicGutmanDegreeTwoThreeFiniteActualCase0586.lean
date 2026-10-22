/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0586 : Family 10 := level10.get ⟨657,by decide⟩
def sourceMap0586 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,5,0,1,2,3,4,6,7,8,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0586 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,10,11,12,9,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0586_checked : acceptsGraphIso
    (source (graph core0586) (root 10) 0 0) DegreeOneSmallSpectrum1276.graph sourceMap0586=true := by decide +kernel
theorem fusedMap0586_checked : acceptsGraphIso
    (fused (graph core0586) (root 10) 0 0) DegreeOneSmallSpectrum1265.graph fusedMap0586=true := by decide +kernel
theorem certified0586 : Certified (graph core0586) (root 10) 0 0 :=
  of_native_maps core0586 DegreeOneSmallSpectrum1276.graph DegreeOneSmallSpectrum1265.graph
    sourceMap0586 fusedMap0586 sourceMap0586_checked fusedMap0586_checked
    DegreeTwoThreeFiniteComparisons.comparison0586
#print axioms sourceMap0586_checked
#print axioms fusedMap0586_checked
#print axioms certified0586
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
