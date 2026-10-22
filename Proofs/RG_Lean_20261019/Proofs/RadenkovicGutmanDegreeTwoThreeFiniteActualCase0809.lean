/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0809 : Family 10 := level10.get ⟨1226,by decide⟩
def sourceMap0809 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0809 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0809_checked : acceptsGraphIso
    (source (graph core0809) (root 10) 0 0) DegreeOneSmallSpectrum1144.graph sourceMap0809=true := by decide +kernel
theorem fusedMap0809_checked : acceptsGraphIso
    (fused (graph core0809) (root 10) 0 0) DegreeOneSmallSpectrum1139.graph fusedMap0809=true := by decide +kernel
theorem certified0809 : Certified (graph core0809) (root 10) 0 0 :=
  of_native_maps core0809 DegreeOneSmallSpectrum1144.graph DegreeOneSmallSpectrum1139.graph
    sourceMap0809 fusedMap0809 sourceMap0809_checked fusedMap0809_checked
    DegreeTwoThreeFiniteComparisons.comparison0809
#print axioms sourceMap0809_checked
#print axioms fusedMap0809_checked
#print axioms certified0809
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
