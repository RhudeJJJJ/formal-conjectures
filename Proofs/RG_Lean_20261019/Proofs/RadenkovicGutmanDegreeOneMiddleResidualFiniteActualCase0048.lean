/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0048 : Family 5 := level5.get ⟨0,by decide⟩
def sourceMap0048 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,11,12,13,6,7,8,9,10] (sourceLabel 5 2 4 v)
def fusedMap0048 : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11,12,13] (fusedLabel 5 2 4 v)
theorem sourceMap0048_checked : acceptsGraphIso
    (source (graph core0048) (root 5) 2 4) DegreeOneMiddleResidualSpectrum055.graph sourceMap0048=true := by decide +kernel
theorem fusedMap0048_checked : acceptsGraphIso
    (fused (graph core0048) (root 5) 2 4) DegreeOneMiddleResidualSpectrum000.graph fusedMap0048=true := by decide +kernel
theorem certified0048 : Certified (graph core0048) (root 5) 2 4 :=
  of_native_maps core0048 DegreeOneMiddleResidualSpectrum055.graph DegreeOneMiddleResidualSpectrum000.graph
    sourceMap0048 fusedMap0048 sourceMap0048_checked fusedMap0048_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0048
#print axioms sourceMap0048_checked
#print axioms fusedMap0048_checked
#print axioms certified0048
def sourceMap0048swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 5 4 2 v)
def fusedMap0048swap : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11,12,13] (fusedLabel 5 4 2 v)
theorem sourceMap0048swap_checked : acceptsGraphIso
    (source (graph core0048) (root 5) 4 2) DegreeOneMiddleResidualSpectrum055.graph sourceMap0048swap=true := by decide +kernel
theorem fusedMap0048swap_checked : acceptsGraphIso
    (fused (graph core0048) (root 5) 4 2) DegreeOneMiddleResidualSpectrum000.graph fusedMap0048swap=true := by decide +kernel
theorem certified0048swap : Certified (graph core0048) (root 5) 4 2 :=
  of_native_maps core0048 DegreeOneMiddleResidualSpectrum055.graph DegreeOneMiddleResidualSpectrum000.graph
    sourceMap0048swap fusedMap0048swap sourceMap0048swap_checked fusedMap0048swap_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0048
#print axioms sourceMap0048swap_checked
#print axioms fusedMap0048swap_checked
#print axioms certified0048swap
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
