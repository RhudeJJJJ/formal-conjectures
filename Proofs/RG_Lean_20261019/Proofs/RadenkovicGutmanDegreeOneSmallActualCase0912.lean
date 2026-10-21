/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0912 : Family 8 := level8.get ⟨59,by decide⟩
def sourceMap0912 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,11,10,8,9] (sourceLabel 8 0 1 v)
def fusedMap0912 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (fusedLabel 8 0 1 v)
theorem sourceMap0912_checked : acceptsGraphIso
    (source (graph core0912) (root 8) 0 1) DegreeOneSmallSpectrum529.graph sourceMap0912=true := by decide +kernel
theorem fusedMap0912_checked : acceptsGraphIso
    (fused (graph core0912) (root 8) 0 1) DegreeOneSmallSpectrum534.graph fusedMap0912=true := by decide +kernel
theorem certified0912 : Certified (graph core0912) (root 8) 0 1 :=
  of_native_maps core0912 DegreeOneSmallSpectrum529.graph DegreeOneSmallSpectrum534.graph
    sourceMap0912 fusedMap0912 sourceMap0912_checked fusedMap0912_checked
    DegreeOneSmallComparisons.comparison0912
#print axioms sourceMap0912_checked
#print axioms fusedMap0912_checked
#print axioms certified0912
def sourceMap0912swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,11,8,9,10] (sourceLabel 8 1 0 v)
def fusedMap0912swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (fusedLabel 8 1 0 v)
theorem sourceMap0912swap_checked : acceptsGraphIso
    (source (graph core0912) (root 8) 1 0) DegreeOneSmallSpectrum529.graph sourceMap0912swap=true := by decide +kernel
theorem fusedMap0912swap_checked : acceptsGraphIso
    (fused (graph core0912) (root 8) 1 0) DegreeOneSmallSpectrum534.graph fusedMap0912swap=true := by decide +kernel
theorem certified0912swap : Certified (graph core0912) (root 8) 1 0 :=
  of_native_maps core0912 DegreeOneSmallSpectrum529.graph DegreeOneSmallSpectrum534.graph
    sourceMap0912swap fusedMap0912swap sourceMap0912swap_checked fusedMap0912swap_checked
    DegreeOneSmallComparisons.comparison0912
#print axioms sourceMap0912swap_checked
#print axioms fusedMap0912swap_checked
#print axioms certified0912swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
