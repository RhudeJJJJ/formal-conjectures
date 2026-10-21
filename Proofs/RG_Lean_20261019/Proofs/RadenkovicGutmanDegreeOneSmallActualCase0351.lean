/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0351 : Family 6 := level6.get ⟨11,by decide⟩
def sourceMap0351 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,11,7,8,9,10] (sourceLabel 6 0 3 v)
def fusedMap0351 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 0 3 v)
theorem sourceMap0351_checked : acceptsGraphIso
    (source (graph core0351) (root 6) 0 3) DegreeOneSmallSpectrum534.graph sourceMap0351=true := by decide +kernel
theorem fusedMap0351_checked : acceptsGraphIso
    (fused (graph core0351) (root 6) 0 3) DegreeOneSmallSpectrum380.graph fusedMap0351=true := by decide +kernel
theorem certified0351 : Certified (graph core0351) (root 6) 0 3 :=
  of_native_maps core0351 DegreeOneSmallSpectrum534.graph DegreeOneSmallSpectrum380.graph
    sourceMap0351 fusedMap0351 sourceMap0351_checked fusedMap0351_checked
    DegreeOneSmallComparisons.comparison0351
#print axioms sourceMap0351_checked
#print axioms fusedMap0351_checked
#print axioms certified0351
def sourceMap0351swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 6 3 0 v)
def fusedMap0351swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 3 0 v)
theorem sourceMap0351swap_checked : acceptsGraphIso
    (source (graph core0351) (root 6) 3 0) DegreeOneSmallSpectrum534.graph sourceMap0351swap=true := by decide +kernel
theorem fusedMap0351swap_checked : acceptsGraphIso
    (fused (graph core0351) (root 6) 3 0) DegreeOneSmallSpectrum380.graph fusedMap0351swap=true := by decide +kernel
theorem certified0351swap : Certified (graph core0351) (root 6) 3 0 :=
  of_native_maps core0351 DegreeOneSmallSpectrum534.graph DegreeOneSmallSpectrum380.graph
    sourceMap0351swap fusedMap0351swap sourceMap0351swap_checked fusedMap0351swap_checked
    DegreeOneSmallComparisons.comparison0351
#print axioms sourceMap0351swap_checked
#print axioms fusedMap0351swap_checked
#print axioms certified0351swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
