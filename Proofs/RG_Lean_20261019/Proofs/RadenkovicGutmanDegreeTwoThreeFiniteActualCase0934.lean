/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0934 : Family 10 := level10.get ⟨1544,by decide⟩
def sourceMap0934 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (sourceLabel 10 0 0 v)
def fusedMap0934 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0934_checked : acceptsGraphIso
    (source (graph core0934) (root 10) 0 0) DegreeOneSmallSpectrum1998.graph sourceMap0934=true := by decide +kernel
theorem fusedMap0934_checked : acceptsGraphIso
    (fused (graph core0934) (root 10) 0 0) DegreeOneSmallSpectrum1557.graph fusedMap0934=true := by decide +kernel
theorem certified0934 : Certified (graph core0934) (root 10) 0 0 :=
  of_native_maps core0934 DegreeOneSmallSpectrum1998.graph DegreeOneSmallSpectrum1557.graph
    sourceMap0934 fusedMap0934 sourceMap0934_checked fusedMap0934_checked
    DegreeTwoThreeFiniteComparisons.comparison0934
#print axioms sourceMap0934_checked
#print axioms fusedMap0934_checked
#print axioms certified0934
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
