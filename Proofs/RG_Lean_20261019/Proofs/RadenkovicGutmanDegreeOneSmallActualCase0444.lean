/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0444 : Family 6 := level6.get ⟨37,by decide⟩
def sourceMap0444 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 6 1 2 v)
def fusedMap0444 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 1 2 v)
theorem sourceMap0444_checked : acceptsGraphIso
    (source (graph core0444) (root 6) 1 2) SmallGeFourSpectrum117.graph sourceMap0444=true := by decide +kernel
theorem fusedMap0444_checked : acceptsGraphIso
    (fused (graph core0444) (root 6) 1 2) SmallGeFourSpectrum093.graph fusedMap0444=true := by decide +kernel
theorem certified0444 : Certified (graph core0444) (root 6) 1 2 :=
  of_native_maps core0444 SmallGeFourSpectrum117.graph SmallGeFourSpectrum093.graph
    sourceMap0444 fusedMap0444 sourceMap0444_checked fusedMap0444_checked
    DegreeOneSmallComparisons.comparison0444
#print axioms sourceMap0444_checked
#print axioms fusedMap0444_checked
#print axioms certified0444
def sourceMap0444swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,9,10,11,7,8] (sourceLabel 6 2 1 v)
def fusedMap0444swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 2 1 v)
theorem sourceMap0444swap_checked : acceptsGraphIso
    (source (graph core0444) (root 6) 2 1) SmallGeFourSpectrum117.graph sourceMap0444swap=true := by decide +kernel
theorem fusedMap0444swap_checked : acceptsGraphIso
    (fused (graph core0444) (root 6) 2 1) SmallGeFourSpectrum093.graph fusedMap0444swap=true := by decide +kernel
theorem certified0444swap : Certified (graph core0444) (root 6) 2 1 :=
  of_native_maps core0444 SmallGeFourSpectrum117.graph SmallGeFourSpectrum093.graph
    sourceMap0444swap fusedMap0444swap sourceMap0444swap_checked fusedMap0444swap_checked
    DegreeOneSmallComparisons.comparison0444
#print axioms sourceMap0444swap_checked
#print axioms fusedMap0444swap_checked
#print axioms certified0444swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
