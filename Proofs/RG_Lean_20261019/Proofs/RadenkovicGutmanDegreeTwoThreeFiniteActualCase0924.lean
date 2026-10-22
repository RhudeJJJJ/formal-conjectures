/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0924 : Family 10 := level10.get ⟨1504,by decide⟩
def sourceMap0924 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,9,10,11,12,1,2,3,4,5,6,7,8] (sourceLabel 10 0 0 v)
def fusedMap0924 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,9,10,11,12,1,2,3,4,5,6,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0924_checked : acceptsGraphIso
    (source (graph core0924) (root 10) 0 0) DegreeOneSmallSpectrum1355.graph sourceMap0924=true := by decide +kernel
theorem fusedMap0924_checked : acceptsGraphIso
    (fused (graph core0924) (root 10) 0 0) DegreeOneSmallSpectrum1354.graph fusedMap0924=true := by decide +kernel
theorem certified0924 : Certified (graph core0924) (root 10) 0 0 :=
  of_native_maps core0924 DegreeOneSmallSpectrum1355.graph DegreeOneSmallSpectrum1354.graph
    sourceMap0924 fusedMap0924 sourceMap0924_checked fusedMap0924_checked
    DegreeTwoThreeFiniteComparisons.comparison0924
#print axioms sourceMap0924_checked
#print axioms fusedMap0924_checked
#print axioms certified0924
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
