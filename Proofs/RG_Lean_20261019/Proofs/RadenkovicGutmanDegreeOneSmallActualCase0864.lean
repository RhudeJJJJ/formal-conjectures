/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0864 : Family 8 := level8.get ⟨41,by decide⟩
def sourceMap0864 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap0864 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0864_checked : acceptsGraphIso
    (source (graph core0864) (root 8) 0 1) DegreeOneSmallSpectrum444.graph sourceMap0864=true := by decide +kernel
theorem fusedMap0864_checked : acceptsGraphIso
    (fused (graph core0864) (root 8) 0 1) DegreeOneSmallSpectrum446.graph fusedMap0864=true := by decide +kernel
theorem certified0864 : Certified (graph core0864) (root 8) 0 1 :=
  of_native_maps core0864 DegreeOneSmallSpectrum444.graph DegreeOneSmallSpectrum446.graph
    sourceMap0864 fusedMap0864 sourceMap0864_checked fusedMap0864_checked
    DegreeOneSmallComparisons.comparison0864
#print axioms sourceMap0864_checked
#print axioms fusedMap0864_checked
#print axioms certified0864
def sourceMap0864swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap0864swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0864swap_checked : acceptsGraphIso
    (source (graph core0864) (root 8) 1 0) DegreeOneSmallSpectrum444.graph sourceMap0864swap=true := by decide +kernel
theorem fusedMap0864swap_checked : acceptsGraphIso
    (fused (graph core0864) (root 8) 1 0) DegreeOneSmallSpectrum446.graph fusedMap0864swap=true := by decide +kernel
theorem certified0864swap : Certified (graph core0864) (root 8) 1 0 :=
  of_native_maps core0864 DegreeOneSmallSpectrum444.graph DegreeOneSmallSpectrum446.graph
    sourceMap0864swap fusedMap0864swap sourceMap0864swap_checked fusedMap0864swap_checked
    DegreeOneSmallComparisons.comparison0864
#print axioms sourceMap0864swap_checked
#print axioms fusedMap0864swap_checked
#print axioms certified0864swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
