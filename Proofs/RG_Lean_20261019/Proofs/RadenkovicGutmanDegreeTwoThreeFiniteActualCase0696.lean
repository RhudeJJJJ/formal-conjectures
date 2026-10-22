/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0696 : Family 10 := level10.get ⟨952,by decide⟩
def sourceMap0696 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,6,7,8,2,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0696 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,6,7,8,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0696_checked : acceptsGraphIso
    (source (graph core0696) (root 10) 0 0) DegreeOneSmallSpectrum1367.graph sourceMap0696=true := by decide +kernel
theorem fusedMap0696_checked : acceptsGraphIso
    (fused (graph core0696) (root 10) 0 0) DegreeOneSmallSpectrum1316.graph fusedMap0696=true := by decide +kernel
theorem certified0696 : Certified (graph core0696) (root 10) 0 0 :=
  of_native_maps core0696 DegreeOneSmallSpectrum1367.graph DegreeOneSmallSpectrum1316.graph
    sourceMap0696 fusedMap0696 sourceMap0696_checked fusedMap0696_checked
    DegreeTwoThreeFiniteComparisons.comparison0696
#print axioms sourceMap0696_checked
#print axioms fusedMap0696_checked
#print axioms certified0696
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
