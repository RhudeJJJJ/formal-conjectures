/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0829 : Family 10 := level10.get ⟨1282,by decide⟩
def sourceMap0829 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,11,12,7,8,9,10] (sourceLabel 10 0 0 v)
def fusedMap0829 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0829_checked : acceptsGraphIso
    (source (graph core0829) (root 10) 0 0) DegreeOneSmallSpectrum1921.graph sourceMap0829=true := by decide +kernel
theorem fusedMap0829_checked : acceptsGraphIso
    (fused (graph core0829) (root 10) 0 0) DegreeOneSmallSpectrum1916.graph fusedMap0829=true := by decide +kernel
theorem certified0829 : Certified (graph core0829) (root 10) 0 0 :=
  of_native_maps core0829 DegreeOneSmallSpectrum1921.graph DegreeOneSmallSpectrum1916.graph
    sourceMap0829 fusedMap0829 sourceMap0829_checked fusedMap0829_checked
    DegreeTwoThreeFiniteComparisons.comparison0829
#print axioms sourceMap0829_checked
#print axioms fusedMap0829_checked
#print axioms certified0829
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
