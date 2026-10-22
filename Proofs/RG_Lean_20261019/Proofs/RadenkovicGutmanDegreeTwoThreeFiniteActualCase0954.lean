/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0954 : Family 10 := level10.get ⟨1587,by decide⟩
def sourceMap0954 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0954 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0954_checked : acceptsGraphIso
    (source (graph core0954) (root 10) 0 0) DegreeOneSmallSpectrum1654.graph sourceMap0954=true := by decide +kernel
theorem fusedMap0954_checked : acceptsGraphIso
    (fused (graph core0954) (root 10) 0 0) DegreeOneSmallSpectrum1653.graph fusedMap0954=true := by decide +kernel
theorem certified0954 : Certified (graph core0954) (root 10) 0 0 :=
  of_native_maps core0954 DegreeOneSmallSpectrum1654.graph DegreeOneSmallSpectrum1653.graph
    sourceMap0954 fusedMap0954 sourceMap0954_checked fusedMap0954_checked
    DegreeTwoThreeFiniteComparisons.comparison0954
#print axioms sourceMap0954_checked
#print axioms fusedMap0954_checked
#print axioms certified0954
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
