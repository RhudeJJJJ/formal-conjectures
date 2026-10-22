/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0463 : Family 10 := level10.get ⟨275,by decide⟩
def sourceMap0463 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0463 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,10,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap0463_checked : acceptsGraphIso
    (source (graph core0463) (root 10) 0 0) DegreeOneSmallSpectrum1012.graph sourceMap0463=true := by decide +kernel
theorem fusedMap0463_checked : acceptsGraphIso
    (fused (graph core0463) (root 10) 0 0) DegreeOneSmallSpectrum1268.graph fusedMap0463=true := by decide +kernel
theorem certified0463 : Certified (graph core0463) (root 10) 0 0 :=
  of_native_maps core0463 DegreeOneSmallSpectrum1012.graph DegreeOneSmallSpectrum1268.graph
    sourceMap0463 fusedMap0463 sourceMap0463_checked fusedMap0463_checked
    DegreeTwoThreeFiniteComparisons.comparison0463
#print axioms sourceMap0463_checked
#print axioms fusedMap0463_checked
#print axioms certified0463
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
