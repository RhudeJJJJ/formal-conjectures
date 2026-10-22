/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0643 : Family 10 := level10.get ⟨815,by decide⟩
def sourceMap0643 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,6,7,2,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0643 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,6,7,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0643_checked : acceptsGraphIso
    (source (graph core0643) (root 10) 0 0) DegreeOneSmallSpectrum1372.graph sourceMap0643=true := by decide +kernel
theorem fusedMap0643_checked : acceptsGraphIso
    (fused (graph core0643) (root 10) 0 0) DegreeOneSmallSpectrum1321.graph fusedMap0643=true := by decide +kernel
theorem certified0643 : Certified (graph core0643) (root 10) 0 0 :=
  of_native_maps core0643 DegreeOneSmallSpectrum1372.graph DegreeOneSmallSpectrum1321.graph
    sourceMap0643 fusedMap0643 sourceMap0643_checked fusedMap0643_checked
    DegreeTwoThreeFiniteComparisons.comparison0643
#print axioms sourceMap0643_checked
#print axioms fusedMap0643_checked
#print axioms certified0643
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
