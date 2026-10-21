/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0031 : Family 2 := level2.get ⟨0,by decide⟩
def sourceMap0031 : (Vertices 2 ⊕ Fin 1 ⊕ Fin 2) → Fin 6 :=
  fun v => ![0,1,2,5,3,4] (sourceLabel 2 0 1 v)
def fusedMap0031 : (Vertices 2 ⊕ Fin 3) → Fin 6 :=
  fun v => ![0,1,2,3,4,5] (fusedLabel 2 0 1 v)
theorem sourceMap0031_checked : acceptsGraphIso
    (source (graph core0031) (root 2) 0 1) DegreeOneSmallSpectrum007.graph sourceMap0031=true := by decide +kernel
theorem fusedMap0031_checked : acceptsGraphIso
    (fused (graph core0031) (root 2) 0 1) DegreeOneSmallSpectrum004.graph fusedMap0031=true := by decide +kernel
theorem certified0031 : Certified (graph core0031) (root 2) 0 1 :=
  of_native_maps core0031 DegreeOneSmallSpectrum007.graph DegreeOneSmallSpectrum004.graph
    sourceMap0031 fusedMap0031 sourceMap0031_checked fusedMap0031_checked
    DegreeOneSmallComparisons.comparison0031
#print axioms sourceMap0031_checked
#print axioms fusedMap0031_checked
#print axioms certified0031
def sourceMap0031swap : (Vertices 2 ⊕ Fin 2 ⊕ Fin 1) → Fin 6 :=
  fun v => ![0,1,2,3,4,5] (sourceLabel 2 1 0 v)
def fusedMap0031swap : (Vertices 2 ⊕ Fin 3) → Fin 6 :=
  fun v => ![0,1,2,3,4,5] (fusedLabel 2 1 0 v)
theorem sourceMap0031swap_checked : acceptsGraphIso
    (source (graph core0031) (root 2) 1 0) DegreeOneSmallSpectrum007.graph sourceMap0031swap=true := by decide +kernel
theorem fusedMap0031swap_checked : acceptsGraphIso
    (fused (graph core0031) (root 2) 1 0) DegreeOneSmallSpectrum004.graph fusedMap0031swap=true := by decide +kernel
theorem certified0031swap : Certified (graph core0031) (root 2) 1 0 :=
  of_native_maps core0031 DegreeOneSmallSpectrum007.graph DegreeOneSmallSpectrum004.graph
    sourceMap0031swap fusedMap0031swap sourceMap0031swap_checked fusedMap0031swap_checked
    DegreeOneSmallComparisons.comparison0031
#print axioms sourceMap0031swap_checked
#print axioms fusedMap0031swap_checked
#print axioms certified0031swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
