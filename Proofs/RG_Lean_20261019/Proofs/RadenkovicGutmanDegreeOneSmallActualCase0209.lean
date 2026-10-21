/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0209 : Family 5 := level5.get ⟨5,by decide⟩
def sourceMap0209 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,9,6,7,8] (sourceLabel 5 0 2 v)
def fusedMap0209 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 0 2 v)
theorem sourceMap0209_checked : acceptsGraphIso
    (source (graph core0209) (root 5) 0 2) DegreeOneSmallSpectrum106.graph sourceMap0209=true := by decide +kernel
theorem fusedMap0209_checked : acceptsGraphIso
    (fused (graph core0209) (root 5) 0 2) DegreeOneSmallSpectrum074.graph fusedMap0209=true := by decide +kernel
theorem certified0209 : Certified (graph core0209) (root 5) 0 2 :=
  of_native_maps core0209 DegreeOneSmallSpectrum106.graph DegreeOneSmallSpectrum074.graph
    sourceMap0209 fusedMap0209 sourceMap0209_checked fusedMap0209_checked
    DegreeOneSmallComparisons.comparison0209
#print axioms sourceMap0209_checked
#print axioms fusedMap0209_checked
#print axioms certified0209
def sourceMap0209swap : (Vertices 5 ⊕ Fin 3 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 5 2 0 v)
def fusedMap0209swap : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 2 0 v)
theorem sourceMap0209swap_checked : acceptsGraphIso
    (source (graph core0209) (root 5) 2 0) DegreeOneSmallSpectrum106.graph sourceMap0209swap=true := by decide +kernel
theorem fusedMap0209swap_checked : acceptsGraphIso
    (fused (graph core0209) (root 5) 2 0) DegreeOneSmallSpectrum074.graph fusedMap0209swap=true := by decide +kernel
theorem certified0209swap : Certified (graph core0209) (root 5) 2 0 :=
  of_native_maps core0209 DegreeOneSmallSpectrum106.graph DegreeOneSmallSpectrum074.graph
    sourceMap0209swap fusedMap0209swap sourceMap0209swap_checked fusedMap0209swap_checked
    DegreeOneSmallComparisons.comparison0209
#print axioms sourceMap0209swap_checked
#print axioms fusedMap0209swap_checked
#print axioms certified0209swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
