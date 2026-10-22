/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0833 : Family 10 := level10.get ⟨1289,by decide⟩
def sourceMap0833 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0833 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0833_checked : acceptsGraphIso
    (source (graph core0833) (root 10) 0 0) DegreeOneSmallSpectrum1219.graph sourceMap0833=true := by decide +kernel
theorem fusedMap0833_checked : acceptsGraphIso
    (fused (graph core0833) (root 10) 0 0) DegreeOneSmallSpectrum1204.graph fusedMap0833=true := by decide +kernel
theorem certified0833 : Certified (graph core0833) (root 10) 0 0 :=
  of_native_maps core0833 DegreeOneSmallSpectrum1219.graph DegreeOneSmallSpectrum1204.graph
    sourceMap0833 fusedMap0833 sourceMap0833_checked fusedMap0833_checked
    DegreeTwoThreeFiniteComparisons.comparison0833
#print axioms sourceMap0833_checked
#print axioms fusedMap0833_checked
#print axioms certified0833
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
