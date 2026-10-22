/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0050 : Family 5 := level5.get ⟨2,by decide⟩
def sourceMap0050 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 5 2 4 v)
def fusedMap0050 : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 2 4 v)
theorem sourceMap0050_checked : acceptsGraphIso
    (source (graph core0050) (root 5) 2 4) DegreeOneMiddleResidualSpectrum045.graph sourceMap0050=true := by decide +kernel
theorem fusedMap0050_checked : acceptsGraphIso
    (fused (graph core0050) (root 5) 2 4) DegreeTwoThreeSpectrum1722.graph fusedMap0050=true := by decide +kernel
theorem certified0050 : Certified (graph core0050) (root 5) 2 4 :=
  of_native_maps core0050 DegreeOneMiddleResidualSpectrum045.graph DegreeTwoThreeSpectrum1722.graph
    sourceMap0050 fusedMap0050 sourceMap0050_checked fusedMap0050_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0050
#print axioms sourceMap0050_checked
#print axioms fusedMap0050_checked
#print axioms certified0050
def sourceMap0050swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,13,6,7,8] (sourceLabel 5 4 2 v)
def fusedMap0050swap : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 4 2 v)
theorem sourceMap0050swap_checked : acceptsGraphIso
    (source (graph core0050) (root 5) 4 2) DegreeOneMiddleResidualSpectrum045.graph sourceMap0050swap=true := by decide +kernel
theorem fusedMap0050swap_checked : acceptsGraphIso
    (fused (graph core0050) (root 5) 4 2) DegreeTwoThreeSpectrum1722.graph fusedMap0050swap=true := by decide +kernel
theorem certified0050swap : Certified (graph core0050) (root 5) 4 2 :=
  of_native_maps core0050 DegreeOneMiddleResidualSpectrum045.graph DegreeTwoThreeSpectrum1722.graph
    sourceMap0050swap fusedMap0050swap sourceMap0050swap_checked fusedMap0050swap_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0050
#print axioms sourceMap0050swap_checked
#print axioms fusedMap0050swap_checked
#print axioms certified0050swap
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
