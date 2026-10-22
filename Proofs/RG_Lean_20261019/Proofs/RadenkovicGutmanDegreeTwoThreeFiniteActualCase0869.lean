/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0869 : Family 10 := level10.get ⟨1374,by decide⟩
def sourceMap0869 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0869 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0869_checked : acceptsGraphIso
    (source (graph core0869) (root 10) 0 0) DegreeOneSmallSpectrum1422.graph sourceMap0869=true := by decide +kernel
theorem fusedMap0869_checked : acceptsGraphIso
    (fused (graph core0869) (root 10) 0 0) DegreeOneSmallSpectrum1421.graph fusedMap0869=true := by decide +kernel
theorem certified0869 : Certified (graph core0869) (root 10) 0 0 :=
  of_native_maps core0869 DegreeOneSmallSpectrum1422.graph DegreeOneSmallSpectrum1421.graph
    sourceMap0869 fusedMap0869 sourceMap0869_checked fusedMap0869_checked
    DegreeTwoThreeFiniteComparisons.comparison0869
#print axioms sourceMap0869_checked
#print axioms fusedMap0869_checked
#print axioms certified0869
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
