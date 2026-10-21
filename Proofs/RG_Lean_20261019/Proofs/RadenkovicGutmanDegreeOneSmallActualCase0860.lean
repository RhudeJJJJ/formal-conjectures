/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0860 : Family 8 := level8.get ⟨40,by decide⟩
def sourceMap0860 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap0860 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0860_checked : acceptsGraphIso
    (source (graph core0860) (root 8) 0 1) DegreeOneSmallSpectrum438.graph sourceMap0860=true := by decide +kernel
theorem fusedMap0860_checked : acceptsGraphIso
    (fused (graph core0860) (root 8) 0 1) DegreeOneSmallSpectrum440.graph fusedMap0860=true := by decide +kernel
theorem certified0860 : Certified (graph core0860) (root 8) 0 1 :=
  of_native_maps core0860 DegreeOneSmallSpectrum438.graph DegreeOneSmallSpectrum440.graph
    sourceMap0860 fusedMap0860 sourceMap0860_checked fusedMap0860_checked
    DegreeOneSmallComparisons.comparison0860
#print axioms sourceMap0860_checked
#print axioms fusedMap0860_checked
#print axioms certified0860
def sourceMap0860swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap0860swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0860swap_checked : acceptsGraphIso
    (source (graph core0860) (root 8) 1 0) DegreeOneSmallSpectrum438.graph sourceMap0860swap=true := by decide +kernel
theorem fusedMap0860swap_checked : acceptsGraphIso
    (fused (graph core0860) (root 8) 1 0) DegreeOneSmallSpectrum440.graph fusedMap0860swap=true := by decide +kernel
theorem certified0860swap : Certified (graph core0860) (root 8) 1 0 :=
  of_native_maps core0860 DegreeOneSmallSpectrum438.graph DegreeOneSmallSpectrum440.graph
    sourceMap0860swap fusedMap0860swap sourceMap0860swap_checked fusedMap0860swap_checked
    DegreeOneSmallComparisons.comparison0860
#print axioms sourceMap0860swap_checked
#print axioms fusedMap0860swap_checked
#print axioms certified0860swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
