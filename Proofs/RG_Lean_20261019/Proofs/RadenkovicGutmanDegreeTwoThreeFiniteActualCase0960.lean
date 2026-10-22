/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0960 : Family 10 := level10.get ⟨1600,by decide⟩
def sourceMap0960 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0960 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0960_checked : acceptsGraphIso
    (source (graph core0960) (root 10) 0 0) DegreeOneSmallSpectrum1680.graph sourceMap0960=true := by decide +kernel
theorem fusedMap0960_checked : acceptsGraphIso
    (fused (graph core0960) (root 10) 0 0) DegreeOneSmallSpectrum1679.graph fusedMap0960=true := by decide +kernel
theorem certified0960 : Certified (graph core0960) (root 10) 0 0 :=
  of_native_maps core0960 DegreeOneSmallSpectrum1680.graph DegreeOneSmallSpectrum1679.graph
    sourceMap0960 fusedMap0960 sourceMap0960_checked fusedMap0960_checked
    DegreeTwoThreeFiniteComparisons.comparison0960
#print axioms sourceMap0960_checked
#print axioms fusedMap0960_checked
#print axioms certified0960
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
