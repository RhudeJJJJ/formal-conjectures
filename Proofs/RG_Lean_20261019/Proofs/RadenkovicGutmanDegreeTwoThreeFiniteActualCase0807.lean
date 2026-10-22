/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0807 : Family 10 := level10.get ⟨1223,by decide⟩
def sourceMap0807 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0807 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0807_checked : acceptsGraphIso
    (source (graph core0807) (root 10) 0 0) DegreeOneSmallSpectrum1287.graph sourceMap0807=true := by decide +kernel
theorem fusedMap0807_checked : acceptsGraphIso
    (fused (graph core0807) (root 10) 0 0) DegreeOneSmallSpectrum1286.graph fusedMap0807=true := by decide +kernel
theorem certified0807 : Certified (graph core0807) (root 10) 0 0 :=
  of_native_maps core0807 DegreeOneSmallSpectrum1287.graph DegreeOneSmallSpectrum1286.graph
    sourceMap0807 fusedMap0807 sourceMap0807_checked fusedMap0807_checked
    DegreeTwoThreeFiniteComparisons.comparison0807
#print axioms sourceMap0807_checked
#print axioms fusedMap0807_checked
#print axioms certified0807
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
