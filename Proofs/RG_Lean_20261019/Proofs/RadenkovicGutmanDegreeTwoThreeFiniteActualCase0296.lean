/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0296 : Family 9 := level9.get ⟨429,by decide⟩
def sourceMap0296 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,6,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0296 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,9,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap0296_checked : acceptsGraphIso
    (source (graph core0296) (root 9) 0 0) DegreeOneSmallSpectrum638.graph sourceMap0296=true := by decide +kernel
theorem fusedMap0296_checked : acceptsGraphIso
    (fused (graph core0296) (root 9) 0 0) DegreeOneSmallSpectrum792.graph fusedMap0296=true := by decide +kernel
theorem certified0296 : Certified (graph core0296) (root 9) 0 0 :=
  of_native_maps core0296 DegreeOneSmallSpectrum638.graph DegreeOneSmallSpectrum792.graph
    sourceMap0296 fusedMap0296 sourceMap0296_checked fusedMap0296_checked
    DegreeTwoThreeFiniteComparisons.comparison0296
#print axioms sourceMap0296_checked
#print axioms fusedMap0296_checked
#print axioms certified0296
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
