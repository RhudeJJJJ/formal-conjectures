/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0247 : Family 5 := level5.get ⟨9,by decide⟩
def sourceMap0247 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (sourceLabel 5 0 4 v)
def fusedMap0247 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 0 4 v)
theorem sourceMap0247_checked : acceptsGraphIso
    (source (graph core0247) (root 5) 0 4) DegreeOneSmallSpectrum528.graph sourceMap0247=true := by decide +kernel
theorem fusedMap0247_checked : acceptsGraphIso
    (fused (graph core0247) (root 5) 0 4) DegreeOneSmallSpectrum380.graph fusedMap0247=true := by decide +kernel
theorem certified0247 : Certified (graph core0247) (root 5) 0 4 :=
  of_native_maps core0247 DegreeOneSmallSpectrum528.graph DegreeOneSmallSpectrum380.graph
    sourceMap0247 fusedMap0247 sourceMap0247_checked fusedMap0247_checked
    DegreeOneSmallComparisons.comparison0247
#print axioms sourceMap0247_checked
#print axioms fusedMap0247_checked
#print axioms certified0247
def sourceMap0247swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,8,9,10,11,7] (sourceLabel 5 4 0 v)
def fusedMap0247swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 4 0 v)
theorem sourceMap0247swap_checked : acceptsGraphIso
    (source (graph core0247) (root 5) 4 0) DegreeOneSmallSpectrum528.graph sourceMap0247swap=true := by decide +kernel
theorem fusedMap0247swap_checked : acceptsGraphIso
    (fused (graph core0247) (root 5) 4 0) DegreeOneSmallSpectrum380.graph fusedMap0247swap=true := by decide +kernel
theorem certified0247swap : Certified (graph core0247) (root 5) 4 0 :=
  of_native_maps core0247 DegreeOneSmallSpectrum528.graph DegreeOneSmallSpectrum380.graph
    sourceMap0247swap fusedMap0247swap sourceMap0247swap_checked fusedMap0247swap_checked
    DegreeOneSmallComparisons.comparison0247
#print axioms sourceMap0247swap_checked
#print axioms fusedMap0247swap_checked
#print axioms certified0247swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
