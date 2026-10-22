/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0991 : Family 10 := level10.get ⟨1688,by decide⟩
def sourceMap0991 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,9,10,11,12,1,2,3,4,5,6,7,8] (sourceLabel 10 0 0 v)
def fusedMap0991 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,9,10,11,12,1,2,3,4,5,6,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0991_checked : acceptsGraphIso
    (source (graph core0991) (root 10) 0 0) DegreeOneSmallSpectrum1538.graph sourceMap0991=true := by decide +kernel
theorem fusedMap0991_checked : acceptsGraphIso
    (fused (graph core0991) (root 10) 0 0) DegreeOneSmallSpectrum1534.graph fusedMap0991=true := by decide +kernel
theorem certified0991 : Certified (graph core0991) (root 10) 0 0 :=
  of_native_maps core0991 DegreeOneSmallSpectrum1538.graph DegreeOneSmallSpectrum1534.graph
    sourceMap0991 fusedMap0991 sourceMap0991_checked fusedMap0991_checked
    DegreeTwoThreeFiniteComparisons.comparison0991
#print axioms sourceMap0991_checked
#print axioms fusedMap0991_checked
#print axioms certified0991
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
