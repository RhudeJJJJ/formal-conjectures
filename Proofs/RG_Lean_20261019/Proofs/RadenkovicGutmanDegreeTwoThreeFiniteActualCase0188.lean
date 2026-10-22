/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0188 : Family 9 := level9.get ⟨123,by decide⟩
def sourceMap0188 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0188 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,3,4,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap0188_checked : acceptsGraphIso
    (source (graph core0188) (root 9) 0 0) DegreeOneSmallSpectrum534.graph sourceMap0188=true := by decide +kernel
theorem fusedMap0188_checked : acceptsGraphIso
    (fused (graph core0188) (root 9) 0 0) DegreeOneSmallSpectrum518.graph fusedMap0188=true := by decide +kernel
theorem certified0188 : Certified (graph core0188) (root 9) 0 0 :=
  of_native_maps core0188 DegreeOneSmallSpectrum534.graph DegreeOneSmallSpectrum518.graph
    sourceMap0188 fusedMap0188 sourceMap0188_checked fusedMap0188_checked
    DegreeTwoThreeFiniteComparisons.comparison0188
#print axioms sourceMap0188_checked
#print axioms fusedMap0188_checked
#print axioms certified0188
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
