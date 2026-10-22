/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0184 : Family 6 := level6.get ⟨12,by decide⟩
def sourceMap0184 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 6 2 4 v)
def fusedMap0184 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap0184_checked : acceptsGraphIso
    (source (graph core0184) (root 6) 2 4) DegreeOneMiddleResidualSpectrum228.graph sourceMap0184=true := by decide +kernel
theorem fusedMap0184_checked : acceptsGraphIso
    (fused (graph core0184) (root 6) 2 4) DegreeTwoThreeSpectrum2365.graph fusedMap0184=true := by decide +kernel
theorem certified0184 : Certified (graph core0184) (root 6) 2 4 :=
  of_native_maps core0184 DegreeOneMiddleResidualSpectrum228.graph DegreeTwoThreeSpectrum2365.graph
    sourceMap0184 fusedMap0184 sourceMap0184_checked fusedMap0184_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0184
#print axioms sourceMap0184_checked
#print axioms fusedMap0184_checked
#print axioms certified0184
def sourceMap0184swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,7,8,9] (sourceLabel 6 4 2 v)
def fusedMap0184swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap0184swap_checked : acceptsGraphIso
    (source (graph core0184) (root 6) 4 2) DegreeOneMiddleResidualSpectrum228.graph sourceMap0184swap=true := by decide +kernel
theorem fusedMap0184swap_checked : acceptsGraphIso
    (fused (graph core0184) (root 6) 4 2) DegreeTwoThreeSpectrum2365.graph fusedMap0184swap=true := by decide +kernel
theorem certified0184swap : Certified (graph core0184) (root 6) 4 2 :=
  of_native_maps core0184 DegreeOneMiddleResidualSpectrum228.graph DegreeTwoThreeSpectrum2365.graph
    sourceMap0184swap fusedMap0184swap sourceMap0184swap_checked fusedMap0184swap_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0184
#print axioms sourceMap0184swap_checked
#print axioms fusedMap0184swap_checked
#print axioms certified0184swap
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
