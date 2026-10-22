/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0864 : Family 10 := level10.get ⟨1364,by decide⟩
def sourceMap0864 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0864 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0864_checked : acceptsGraphIso
    (source (graph core0864) (root 10) 0 0) DegreeOneSmallSpectrum1948.graph sourceMap0864=true := by decide +kernel
theorem fusedMap0864_checked : acceptsGraphIso
    (fused (graph core0864) (root 10) 0 0) DegreeOneSmallSpectrum1924.graph fusedMap0864=true := by decide +kernel
theorem certified0864 : Certified (graph core0864) (root 10) 0 0 :=
  of_native_maps core0864 DegreeOneSmallSpectrum1948.graph DegreeOneSmallSpectrum1924.graph
    sourceMap0864 fusedMap0864 sourceMap0864_checked fusedMap0864_checked
    DegreeTwoThreeFiniteComparisons.comparison0864
#print axioms sourceMap0864_checked
#print axioms fusedMap0864_checked
#print axioms certified0864
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
