/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0051 : Family 5 := level5.get ⟨3,by decide⟩
def sourceMap0051 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 5 2 4 v)
def fusedMap0051 : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 2 4 v)
theorem sourceMap0051_checked : acceptsGraphIso
    (source (graph core0051) (root 5) 2 4) DegreeOneMiddleResidualSpectrum054.graph sourceMap0051=true := by decide +kernel
theorem fusedMap0051_checked : acceptsGraphIso
    (fused (graph core0051) (root 5) 2 4) DegreeTwoThreeSpectrum1728.graph fusedMap0051=true := by decide +kernel
theorem certified0051 : Certified (graph core0051) (root 5) 2 4 :=
  of_native_maps core0051 DegreeOneMiddleResidualSpectrum054.graph DegreeTwoThreeSpectrum1728.graph
    sourceMap0051 fusedMap0051 sourceMap0051_checked fusedMap0051_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0051
#print axioms sourceMap0051_checked
#print axioms fusedMap0051_checked
#print axioms certified0051
def sourceMap0051swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,13,6,7,8] (sourceLabel 5 4 2 v)
def fusedMap0051swap : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 4 2 v)
theorem sourceMap0051swap_checked : acceptsGraphIso
    (source (graph core0051) (root 5) 4 2) DegreeOneMiddleResidualSpectrum054.graph sourceMap0051swap=true := by decide +kernel
theorem fusedMap0051swap_checked : acceptsGraphIso
    (fused (graph core0051) (root 5) 4 2) DegreeTwoThreeSpectrum1728.graph fusedMap0051swap=true := by decide +kernel
theorem certified0051swap : Certified (graph core0051) (root 5) 4 2 :=
  of_native_maps core0051 DegreeOneMiddleResidualSpectrum054.graph DegreeTwoThreeSpectrum1728.graph
    sourceMap0051swap fusedMap0051swap sourceMap0051swap_checked fusedMap0051swap_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0051
#print axioms sourceMap0051swap_checked
#print axioms fusedMap0051swap_checked
#print axioms certified0051swap
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
