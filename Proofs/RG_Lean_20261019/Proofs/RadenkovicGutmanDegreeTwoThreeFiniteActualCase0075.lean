/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0075 : Family 8 := level8.get ⟨51,by decide⟩
def sourceMap0075 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![6,5,0,1,2,3,4,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap0075 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,5,0,1,2,3,4,7,8,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0075_checked : acceptsGraphIso
    (source (graph core0075) (root 8) 0 0) DegreeOneSmallSpectrum191.graph sourceMap0075=true := by decide +kernel
theorem fusedMap0075_checked : acceptsGraphIso
    (fused (graph core0075) (root 8) 0 0) DegreeOneSmallSpectrum190.graph fusedMap0075=true := by decide +kernel
theorem certified0075 : Certified (graph core0075) (root 8) 0 0 :=
  of_native_maps core0075 DegreeOneSmallSpectrum191.graph DegreeOneSmallSpectrum190.graph
    sourceMap0075 fusedMap0075 sourceMap0075_checked fusedMap0075_checked
    DegreeTwoThreeFiniteComparisons.comparison0075
#print axioms sourceMap0075_checked
#print axioms fusedMap0075_checked
#print axioms certified0075
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
