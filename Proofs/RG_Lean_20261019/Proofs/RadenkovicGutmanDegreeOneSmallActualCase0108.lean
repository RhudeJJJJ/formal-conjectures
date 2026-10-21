/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0108 : Family 4 := level4.get ⟨0,by decide⟩
def sourceMap0108 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,9,10,11,5,6,7,8] (sourceLabel 4 2 3 v)
def fusedMap0108 : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9,10,11] (fusedLabel 4 2 3 v)
theorem sourceMap0108_checked : acceptsGraphIso
    (source (graph core0108) (root 4) 2 3) DegreeOneSmallSpectrum585.graph sourceMap0108=true := by decide +kernel
theorem fusedMap0108_checked : acceptsGraphIso
    (fused (graph core0108) (root 4) 2 3) DegreeOneSmallSpectrum369.graph fusedMap0108=true := by decide +kernel
theorem certified0108 : Certified (graph core0108) (root 4) 2 3 :=
  of_native_maps core0108 DegreeOneSmallSpectrum585.graph DegreeOneSmallSpectrum369.graph
    sourceMap0108 fusedMap0108 sourceMap0108_checked fusedMap0108_checked
    DegreeOneSmallComparisons.comparison0108
#print axioms sourceMap0108_checked
#print axioms fusedMap0108_checked
#print axioms certified0108
def sourceMap0108swap : (Vertices 4 ⊕ Fin 4 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 4 3 2 v)
def fusedMap0108swap : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9,10,11] (fusedLabel 4 3 2 v)
theorem sourceMap0108swap_checked : acceptsGraphIso
    (source (graph core0108) (root 4) 3 2) DegreeOneSmallSpectrum585.graph sourceMap0108swap=true := by decide +kernel
theorem fusedMap0108swap_checked : acceptsGraphIso
    (fused (graph core0108) (root 4) 3 2) DegreeOneSmallSpectrum369.graph fusedMap0108swap=true := by decide +kernel
theorem certified0108swap : Certified (graph core0108) (root 4) 3 2 :=
  of_native_maps core0108 DegreeOneSmallSpectrum585.graph DegreeOneSmallSpectrum369.graph
    sourceMap0108swap fusedMap0108swap sourceMap0108swap_checked fusedMap0108swap_checked
    DegreeOneSmallComparisons.comparison0108
#print axioms sourceMap0108swap_checked
#print axioms fusedMap0108swap_checked
#print axioms certified0108swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
