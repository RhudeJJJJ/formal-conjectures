/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0980 : Family 10 := level10.get ⟨1650,by decide⟩
def sourceMap0980 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0980 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0980_checked : acceptsGraphIso
    (source (graph core0980) (root 10) 0 0) DegreeOneSmallSpectrum1793.graph sourceMap0980=true := by decide +kernel
theorem fusedMap0980_checked : acceptsGraphIso
    (fused (graph core0980) (root 10) 0 0) DegreeOneSmallSpectrum1792.graph fusedMap0980=true := by decide +kernel
theorem certified0980 : Certified (graph core0980) (root 10) 0 0 :=
  of_native_maps core0980 DegreeOneSmallSpectrum1793.graph DegreeOneSmallSpectrum1792.graph
    sourceMap0980 fusedMap0980 sourceMap0980_checked fusedMap0980_checked
    DegreeTwoThreeFiniteComparisons.comparison0980
#print axioms sourceMap0980_checked
#print axioms fusedMap0980_checked
#print axioms certified0980
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
