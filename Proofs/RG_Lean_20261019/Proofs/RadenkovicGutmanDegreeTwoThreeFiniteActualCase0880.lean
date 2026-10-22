/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0880 : Family 10 := level10.get ⟨1394,by decide⟩
def sourceMap0880 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0880 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0880_checked : acceptsGraphIso
    (source (graph core0880) (root 10) 0 0) DegreeOneSmallSpectrum1372.graph sourceMap0880=true := by decide +kernel
theorem fusedMap0880_checked : acceptsGraphIso
    (fused (graph core0880) (root 10) 0 0) DegreeOneSmallSpectrum1368.graph fusedMap0880=true := by decide +kernel
theorem certified0880 : Certified (graph core0880) (root 10) 0 0 :=
  of_native_maps core0880 DegreeOneSmallSpectrum1372.graph DegreeOneSmallSpectrum1368.graph
    sourceMap0880 fusedMap0880 sourceMap0880_checked fusedMap0880_checked
    DegreeTwoThreeFiniteComparisons.comparison0880
#print axioms sourceMap0880_checked
#print axioms fusedMap0880_checked
#print axioms certified0880
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
