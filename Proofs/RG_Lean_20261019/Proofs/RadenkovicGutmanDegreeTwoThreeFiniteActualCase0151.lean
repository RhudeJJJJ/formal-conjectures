/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0151 : Family 8 := level8.get ⟨244,by decide⟩
def sourceMap0151 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap0151 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0151_checked : acceptsGraphIso
    (source (graph core0151) (root 8) 0 0) DegreeOneSmallSpectrum338.graph sourceMap0151=true := by decide +kernel
theorem fusedMap0151_checked : acceptsGraphIso
    (fused (graph core0151) (root 8) 0 0) DegreeOneSmallSpectrum337.graph fusedMap0151=true := by decide +kernel
theorem certified0151 : Certified (graph core0151) (root 8) 0 0 :=
  of_native_maps core0151 DegreeOneSmallSpectrum338.graph DegreeOneSmallSpectrum337.graph
    sourceMap0151 fusedMap0151 sourceMap0151_checked fusedMap0151_checked
    DegreeTwoThreeFiniteComparisons.comparison0151
#print axioms sourceMap0151_checked
#print axioms fusedMap0151_checked
#print axioms certified0151
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
