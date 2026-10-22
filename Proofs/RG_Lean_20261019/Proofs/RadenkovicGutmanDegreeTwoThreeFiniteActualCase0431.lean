/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0431 : Family 10 := level10.get ⟨161,by decide⟩
def sourceMap0431 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,7,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0431 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0431_checked : acceptsGraphIso
    (source (graph core0431) (root 10) 0 0) DegreeOneSmallSpectrum1037.graph sourceMap0431=true := by decide +kernel
theorem fusedMap0431_checked : acceptsGraphIso
    (fused (graph core0431) (root 10) 0 0) DegreeOneSmallSpectrum928.graph fusedMap0431=true := by decide +kernel
theorem certified0431 : Certified (graph core0431) (root 10) 0 0 :=
  of_native_maps core0431 DegreeOneSmallSpectrum1037.graph DegreeOneSmallSpectrum928.graph
    sourceMap0431 fusedMap0431 sourceMap0431_checked fusedMap0431_checked
    DegreeTwoThreeFiniteComparisons.comparison0431
#print axioms sourceMap0431_checked
#print axioms fusedMap0431_checked
#print axioms certified0431
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
