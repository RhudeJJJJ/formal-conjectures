/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0842 : Family 10 := level10.get ⟨1313,by decide⟩
def sourceMap0842 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0842 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0842_checked : acceptsGraphIso
    (source (graph core0842) (root 10) 0 0) DegreeOneSmallSpectrum1362.graph sourceMap0842=true := by decide +kernel
theorem fusedMap0842_checked : acceptsGraphIso
    (fused (graph core0842) (root 10) 0 0) DegreeOneSmallSpectrum1361.graph fusedMap0842=true := by decide +kernel
theorem certified0842 : Certified (graph core0842) (root 10) 0 0 :=
  of_native_maps core0842 DegreeOneSmallSpectrum1362.graph DegreeOneSmallSpectrum1361.graph
    sourceMap0842 fusedMap0842 sourceMap0842_checked fusedMap0842_checked
    DegreeTwoThreeFiniteComparisons.comparison0842
#print axioms sourceMap0842_checked
#print axioms fusedMap0842_checked
#print axioms certified0842
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
