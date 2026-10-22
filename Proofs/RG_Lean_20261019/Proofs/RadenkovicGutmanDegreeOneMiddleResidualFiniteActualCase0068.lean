/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0068 : Family 8 := level8.get ⟨10,by decide⟩
def sourceMap0068 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0068 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0068_checked : acceptsGraphIso
    (source (graph core0068) (root 8) 2 2) DegreeOneMiddleResidualSpectrum203.graph sourceMap0068=true := by decide +kernel
theorem fusedMap0068_checked : acceptsGraphIso
    (fused (graph core0068) (root 8) 2 2) DegreeTwoThreeSpectrum2333.graph fusedMap0068=true := by decide +kernel
theorem certified0068 : Certified (graph core0068) (root 8) 2 2 :=
  of_native_maps core0068 DegreeOneMiddleResidualSpectrum203.graph DegreeTwoThreeSpectrum2333.graph
    sourceMap0068 fusedMap0068 sourceMap0068_checked fusedMap0068_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0068
#print axioms sourceMap0068_checked
#print axioms fusedMap0068_checked
#print axioms certified0068
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
