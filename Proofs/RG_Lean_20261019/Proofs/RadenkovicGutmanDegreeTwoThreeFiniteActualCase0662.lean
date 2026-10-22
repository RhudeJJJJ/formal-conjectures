/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0662 : Family 10 := level10.get ⟨868,by decide⟩
def sourceMap0662 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0662 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0662_checked : acceptsGraphIso
    (source (graph core0662) (root 10) 0 0) DegreeOneSmallSpectrum1653.graph sourceMap0662=true := by decide +kernel
theorem fusedMap0662_checked : acceptsGraphIso
    (fused (graph core0662) (root 10) 0 0) DegreeOneSmallSpectrum1421.graph fusedMap0662=true := by decide +kernel
theorem certified0662 : Certified (graph core0662) (root 10) 0 0 :=
  of_native_maps core0662 DegreeOneSmallSpectrum1653.graph DegreeOneSmallSpectrum1421.graph
    sourceMap0662 fusedMap0662 sourceMap0662_checked fusedMap0662_checked
    DegreeTwoThreeFiniteComparisons.comparison0662
#print axioms sourceMap0662_checked
#print axioms fusedMap0662_checked
#print axioms certified0662
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
