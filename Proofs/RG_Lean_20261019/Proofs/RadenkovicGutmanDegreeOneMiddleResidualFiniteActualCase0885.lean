/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0885 : Family 10 := level10.get ⟨637,by decide⟩
def sourceMap0885 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0885 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0885_checked : acceptsGraphIso
    (source (graph core0885) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2128.graph sourceMap0885=true := by decide +kernel
theorem fusedMap0885_checked : acceptsGraphIso
    (fused (graph core0885) (root 10) 2 2) DegreeTwoThreeSpectrum5331.graph fusedMap0885=true := by decide +kernel
theorem certified0885 : Certified (graph core0885) (root 10) 2 2 :=
  of_native_maps core0885 DegreeOneMiddleResidualSpectrum2128.graph DegreeTwoThreeSpectrum5331.graph
    sourceMap0885 fusedMap0885 sourceMap0885_checked fusedMap0885_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0885
#print axioms sourceMap0885_checked
#print axioms fusedMap0885_checked
#print axioms certified0885
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
