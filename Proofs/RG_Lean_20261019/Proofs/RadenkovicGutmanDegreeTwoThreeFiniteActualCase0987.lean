/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0987 : Family 10 := level10.get ⟨1665,by decide⟩
def sourceMap0987 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0987 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0987_checked : acceptsGraphIso
    (source (graph core0987) (root 10) 0 0) DegreeOneSmallSpectrum1828.graph sourceMap0987=true := by decide +kernel
theorem fusedMap0987_checked : acceptsGraphIso
    (fused (graph core0987) (root 10) 0 0) DegreeOneSmallSpectrum1827.graph fusedMap0987=true := by decide +kernel
theorem certified0987 : Certified (graph core0987) (root 10) 0 0 :=
  of_native_maps core0987 DegreeOneSmallSpectrum1828.graph DegreeOneSmallSpectrum1827.graph
    sourceMap0987 fusedMap0987 sourceMap0987_checked fusedMap0987_checked
    DegreeTwoThreeFiniteComparisons.comparison0987
#print axioms sourceMap0987_checked
#print axioms fusedMap0987_checked
#print axioms certified0987
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
