/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0941 : Family 10 := level10.get ⟨1558,by decide⟩
def sourceMap0941 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0941 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0941_checked : acceptsGraphIso
    (source (graph core0941) (root 10) 0 0) DegreeOneSmallSpectrum1593.graph sourceMap0941=true := by decide +kernel
theorem fusedMap0941_checked : acceptsGraphIso
    (fused (graph core0941) (root 10) 0 0) DegreeOneSmallSpectrum1592.graph fusedMap0941=true := by decide +kernel
theorem certified0941 : Certified (graph core0941) (root 10) 0 0 :=
  of_native_maps core0941 DegreeOneSmallSpectrum1593.graph DegreeOneSmallSpectrum1592.graph
    sourceMap0941 fusedMap0941 sourceMap0941_checked fusedMap0941_checked
    DegreeTwoThreeFiniteComparisons.comparison0941
#print axioms sourceMap0941_checked
#print axioms fusedMap0941_checked
#print axioms certified0941
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
