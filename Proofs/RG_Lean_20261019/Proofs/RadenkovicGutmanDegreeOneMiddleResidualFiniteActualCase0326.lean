/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0326 : Family 9 := level9.get ⟨187,by decide⟩
def sourceMap0326 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,7,8,9,10,11,12] (sourceLabel 9 2 2 v)
def fusedMap0326 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0326_checked : acceptsGraphIso
    (source (graph core0326) (root 9) 2 2) DegreeOneMiddleResidualSpectrum812.graph sourceMap0326=true := by decide +kernel
theorem fusedMap0326_checked : acceptsGraphIso
    (fused (graph core0326) (root 9) 2 2) DegreeTwoThreeSpectrum3959.graph fusedMap0326=true := by decide +kernel
theorem certified0326 : Certified (graph core0326) (root 9) 2 2 :=
  of_native_maps core0326 DegreeOneMiddleResidualSpectrum812.graph DegreeTwoThreeSpectrum3959.graph
    sourceMap0326 fusedMap0326 sourceMap0326_checked fusedMap0326_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0326
#print axioms sourceMap0326_checked
#print axioms fusedMap0326_checked
#print axioms certified0326
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
