/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0975 : Family 10 := level10.get ⟨1638,by decide⟩
def sourceMap0975 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0975 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0975_checked : acceptsGraphIso
    (source (graph core0975) (root 10) 0 0) DegreeOneSmallSpectrum1760.graph sourceMap0975=true := by decide +kernel
theorem fusedMap0975_checked : acceptsGraphIso
    (fused (graph core0975) (root 10) 0 0) DegreeOneSmallSpectrum1759.graph fusedMap0975=true := by decide +kernel
theorem certified0975 : Certified (graph core0975) (root 10) 0 0 :=
  of_native_maps core0975 DegreeOneSmallSpectrum1760.graph DegreeOneSmallSpectrum1759.graph
    sourceMap0975 fusedMap0975 sourceMap0975_checked fusedMap0975_checked
    DegreeTwoThreeFiniteComparisons.comparison0975
#print axioms sourceMap0975_checked
#print axioms fusedMap0975_checked
#print axioms certified0975
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
