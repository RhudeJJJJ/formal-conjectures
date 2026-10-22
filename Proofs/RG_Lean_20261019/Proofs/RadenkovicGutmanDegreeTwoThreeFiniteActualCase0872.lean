/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0872 : Family 10 := level10.get ⟨1379,by decide⟩
def sourceMap0872 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0872 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0872_checked : acceptsGraphIso
    (source (graph core0872) (root 10) 0 0) DegreeOneSmallSpectrum1221.graph sourceMap0872=true := by decide +kernel
theorem fusedMap0872_checked : acceptsGraphIso
    (fused (graph core0872) (root 10) 0 0) DegreeOneSmallSpectrum1206.graph fusedMap0872=true := by decide +kernel
theorem certified0872 : Certified (graph core0872) (root 10) 0 0 :=
  of_native_maps core0872 DegreeOneSmallSpectrum1221.graph DegreeOneSmallSpectrum1206.graph
    sourceMap0872 fusedMap0872 sourceMap0872_checked fusedMap0872_checked
    DegreeTwoThreeFiniteComparisons.comparison0872
#print axioms sourceMap0872_checked
#print axioms fusedMap0872_checked
#print axioms certified0872
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
