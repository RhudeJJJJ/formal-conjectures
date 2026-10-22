/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0879 : Family 10 := level10.get ⟨1393,by decide⟩
def sourceMap0879 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0879 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0879_checked : acceptsGraphIso
    (source (graph core0879) (root 10) 0 0) DegreeOneSmallSpectrum1321.graph sourceMap0879=true := by decide +kernel
theorem fusedMap0879_checked : acceptsGraphIso
    (fused (graph core0879) (root 10) 0 0) DegreeOneSmallSpectrum1317.graph fusedMap0879=true := by decide +kernel
theorem certified0879 : Certified (graph core0879) (root 10) 0 0 :=
  of_native_maps core0879 DegreeOneSmallSpectrum1321.graph DegreeOneSmallSpectrum1317.graph
    sourceMap0879 fusedMap0879 sourceMap0879_checked fusedMap0879_checked
    DegreeTwoThreeFiniteComparisons.comparison0879
#print axioms sourceMap0879_checked
#print axioms fusedMap0879_checked
#print axioms certified0879
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
