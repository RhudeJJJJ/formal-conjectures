/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0976 : Family 10 := level10.get ⟨1639,by decide⟩
def sourceMap0976 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0976 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0976_checked : acceptsGraphIso
    (source (graph core0976) (root 10) 0 0) DegreeOneSmallSpectrum1769.graph sourceMap0976=true := by decide +kernel
theorem fusedMap0976_checked : acceptsGraphIso
    (fused (graph core0976) (root 10) 0 0) DegreeOneSmallSpectrum1768.graph fusedMap0976=true := by decide +kernel
theorem certified0976 : Certified (graph core0976) (root 10) 0 0 :=
  of_native_maps core0976 DegreeOneSmallSpectrum1769.graph DegreeOneSmallSpectrum1768.graph
    sourceMap0976 fusedMap0976 sourceMap0976_checked fusedMap0976_checked
    DegreeTwoThreeFiniteComparisons.comparison0976
#print axioms sourceMap0976_checked
#print axioms fusedMap0976_checked
#print axioms certified0976
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
