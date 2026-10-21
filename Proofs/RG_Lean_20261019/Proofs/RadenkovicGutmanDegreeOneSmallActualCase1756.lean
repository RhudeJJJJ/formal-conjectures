/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1756 : Family 9 := level9.get ⟨600,by decide⟩
def sourceMap1756 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1756 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1756_checked : acceptsGraphIso
    (source (graph core1756) (root 9) 0 1) DegreeOneSmallSpectrum1776.graph sourceMap1756=true := by decide +kernel
theorem fusedMap1756_checked : acceptsGraphIso
    (fused (graph core1756) (root 9) 0 1) DegreeOneSmallSpectrum1777.graph fusedMap1756=true := by decide +kernel
theorem certified1756 : Certified (graph core1756) (root 9) 0 1 :=
  of_native_maps core1756 DegreeOneSmallSpectrum1776.graph DegreeOneSmallSpectrum1777.graph
    sourceMap1756 fusedMap1756 sourceMap1756_checked fusedMap1756_checked
    DegreeOneSmallComparisons.comparison1756
#print axioms sourceMap1756_checked
#print axioms fusedMap1756_checked
#print axioms certified1756
def sourceMap1756swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1756swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1756swap_checked : acceptsGraphIso
    (source (graph core1756) (root 9) 1 0) DegreeOneSmallSpectrum1776.graph sourceMap1756swap=true := by decide +kernel
theorem fusedMap1756swap_checked : acceptsGraphIso
    (fused (graph core1756) (root 9) 1 0) DegreeOneSmallSpectrum1777.graph fusedMap1756swap=true := by decide +kernel
theorem certified1756swap : Certified (graph core1756) (root 9) 1 0 :=
  of_native_maps core1756 DegreeOneSmallSpectrum1776.graph DegreeOneSmallSpectrum1777.graph
    sourceMap1756swap fusedMap1756swap sourceMap1756swap_checked fusedMap1756swap_checked
    DegreeOneSmallComparisons.comparison1756
#print axioms sourceMap1756swap_checked
#print axioms fusedMap1756swap_checked
#print axioms certified1756swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
