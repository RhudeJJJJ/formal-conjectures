/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0680 : Family 10 := level10.get ⟨912,by decide⟩
def sourceMap0680 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0680 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0680_checked : acceptsGraphIso
    (source (graph core0680) (root 10) 0 0) DegreeOneSmallSpectrum1499.graph sourceMap0680=true := by decide +kernel
theorem fusedMap0680_checked : acceptsGraphIso
    (fused (graph core0680) (root 10) 0 0) DegreeOneSmallSpectrum1489.graph fusedMap0680=true := by decide +kernel
theorem certified0680 : Certified (graph core0680) (root 10) 0 0 :=
  of_native_maps core0680 DegreeOneSmallSpectrum1499.graph DegreeOneSmallSpectrum1489.graph
    sourceMap0680 fusedMap0680 sourceMap0680_checked fusedMap0680_checked
    DegreeTwoThreeFiniteComparisons.comparison0680
#print axioms sourceMap0680_checked
#print axioms fusedMap0680_checked
#print axioms certified0680
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
