/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0864 : Family 10 := level10.get ⟨598,by decide⟩
def sourceMap0864 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0864 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0864_checked : acceptsGraphIso
    (source (graph core0864) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2094.graph sourceMap0864=true := by decide +kernel
theorem fusedMap0864_checked : acceptsGraphIso
    (fused (graph core0864) (root 10) 2 2) DegreeTwoThreeSpectrum5273.graph fusedMap0864=true := by decide +kernel
theorem certified0864 : Certified (graph core0864) (root 10) 2 2 :=
  of_native_maps core0864 DegreeOneMiddleResidualSpectrum2094.graph DegreeTwoThreeSpectrum5273.graph
    sourceMap0864 fusedMap0864 sourceMap0864_checked fusedMap0864_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0864
#print axioms sourceMap0864_checked
#print axioms fusedMap0864_checked
#print axioms certified0864
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
