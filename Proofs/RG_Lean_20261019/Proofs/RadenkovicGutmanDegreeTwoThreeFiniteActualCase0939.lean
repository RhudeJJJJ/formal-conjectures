/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0939 : Family 10 := level10.get ⟨1554,by decide⟩
def sourceMap0939 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0939 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0939_checked : acceptsGraphIso
    (source (graph core0939) (root 10) 0 0) DegreeOneSmallSpectrum1585.graph sourceMap0939=true := by decide +kernel
theorem fusedMap0939_checked : acceptsGraphIso
    (fused (graph core0939) (root 10) 0 0) DegreeOneSmallSpectrum1584.graph fusedMap0939=true := by decide +kernel
theorem certified0939 : Certified (graph core0939) (root 10) 0 0 :=
  of_native_maps core0939 DegreeOneSmallSpectrum1585.graph DegreeOneSmallSpectrum1584.graph
    sourceMap0939 fusedMap0939 sourceMap0939_checked fusedMap0939_checked
    DegreeTwoThreeFiniteComparisons.comparison0939
#print axioms sourceMap0939_checked
#print axioms fusedMap0939_checked
#print axioms certified0939
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
