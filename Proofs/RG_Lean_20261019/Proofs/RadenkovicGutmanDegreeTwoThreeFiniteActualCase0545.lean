/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0545 : Family 10 := level10.get ⟨532,by decide⟩
def sourceMap0545 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0545 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0545_checked : acceptsGraphIso
    (source (graph core0545) (root 10) 0 0) DegreeTwoThreeSpectrum871.graph sourceMap0545=true := by decide +kernel
theorem fusedMap0545_checked : acceptsGraphIso
    (fused (graph core0545) (root 10) 0 0) DegreeOneSmallSpectrum1031.graph fusedMap0545=true := by decide +kernel
theorem certified0545 : Certified (graph core0545) (root 10) 0 0 :=
  of_native_maps core0545 DegreeTwoThreeSpectrum871.graph DegreeOneSmallSpectrum1031.graph
    sourceMap0545 fusedMap0545 sourceMap0545_checked fusedMap0545_checked
    DegreeTwoThreeFiniteComparisons.comparison0545
#print axioms sourceMap0545_checked
#print axioms fusedMap0545_checked
#print axioms certified0545
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
