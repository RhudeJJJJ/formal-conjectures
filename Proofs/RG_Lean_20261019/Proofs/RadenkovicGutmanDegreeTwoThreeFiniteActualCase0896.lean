/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0896 : Family 10 := level10.get ⟨1439,by decide⟩
def sourceMap0896 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0896 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0896_checked : acceptsGraphIso
    (source (graph core0896) (root 10) 0 0) DegreeOneSmallSpectrum1953.graph sourceMap0896=true := by decide +kernel
theorem fusedMap0896_checked : acceptsGraphIso
    (fused (graph core0896) (root 10) 0 0) DegreeOneSmallSpectrum1929.graph fusedMap0896=true := by decide +kernel
theorem certified0896 : Certified (graph core0896) (root 10) 0 0 :=
  of_native_maps core0896 DegreeOneSmallSpectrum1953.graph DegreeOneSmallSpectrum1929.graph
    sourceMap0896 fusedMap0896 sourceMap0896_checked fusedMap0896_checked
    DegreeTwoThreeFiniteComparisons.comparison0896
#print axioms sourceMap0896_checked
#print axioms fusedMap0896_checked
#print axioms certified0896
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
