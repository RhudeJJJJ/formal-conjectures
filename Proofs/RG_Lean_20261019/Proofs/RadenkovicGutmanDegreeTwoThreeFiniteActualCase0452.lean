/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0452 : Family 10 := level10.get ⟨237,by decide⟩
def sourceMap0452 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0452 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0452_checked : acceptsGraphIso
    (source (graph core0452) (root 10) 0 0) DegreeOneSmallSpectrum1028.graph sourceMap0452=true := by decide +kernel
theorem fusedMap0452_checked : acceptsGraphIso
    (fused (graph core0452) (root 10) 0 0) DegreeOneSmallSpectrum1172.graph fusedMap0452=true := by decide +kernel
theorem certified0452 : Certified (graph core0452) (root 10) 0 0 :=
  of_native_maps core0452 DegreeOneSmallSpectrum1028.graph DegreeOneSmallSpectrum1172.graph
    sourceMap0452 fusedMap0452 sourceMap0452_checked fusedMap0452_checked
    DegreeTwoThreeFiniteComparisons.comparison0452
#print axioms sourceMap0452_checked
#print axioms fusedMap0452_checked
#print axioms certified0452
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
