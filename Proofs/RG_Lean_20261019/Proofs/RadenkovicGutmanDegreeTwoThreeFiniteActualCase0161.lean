/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0161 : Family 9 := level9.get ⟨15,by decide⟩
def sourceMap0161 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,7,8,9,10,11,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0161 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,6,0,1,2,3,4,5,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0161_checked : acceptsGraphIso
    (source (graph core0161) (root 9) 0 0) DegreeOneSmallSpectrum420.graph sourceMap0161=true := by decide +kernel
theorem fusedMap0161_checked : acceptsGraphIso
    (fused (graph core0161) (root 9) 0 0) DegreeOneSmallSpectrum375.graph fusedMap0161=true := by decide +kernel
theorem certified0161 : Certified (graph core0161) (root 9) 0 0 :=
  of_native_maps core0161 DegreeOneSmallSpectrum420.graph DegreeOneSmallSpectrum375.graph
    sourceMap0161 fusedMap0161 sourceMap0161_checked fusedMap0161_checked
    DegreeTwoThreeFiniteComparisons.comparison0161
#print axioms sourceMap0161_checked
#print axioms fusedMap0161_checked
#print axioms certified0161
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
