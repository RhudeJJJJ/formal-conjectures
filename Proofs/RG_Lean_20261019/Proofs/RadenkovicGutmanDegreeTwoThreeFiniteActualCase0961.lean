/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0961 : Family 10 := level10.get ⟨1602,by decide⟩
def sourceMap0961 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0961 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0961_checked : acceptsGraphIso
    (source (graph core0961) (root 10) 0 0) DegreeOneSmallSpectrum1686.graph sourceMap0961=true := by decide +kernel
theorem fusedMap0961_checked : acceptsGraphIso
    (fused (graph core0961) (root 10) 0 0) DegreeOneSmallSpectrum1685.graph fusedMap0961=true := by decide +kernel
theorem certified0961 : Certified (graph core0961) (root 10) 0 0 :=
  of_native_maps core0961 DegreeOneSmallSpectrum1686.graph DegreeOneSmallSpectrum1685.graph
    sourceMap0961 fusedMap0961 sourceMap0961_checked fusedMap0961_checked
    DegreeTwoThreeFiniteComparisons.comparison0961
#print axioms sourceMap0961_checked
#print axioms fusedMap0961_checked
#print axioms certified0961
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
