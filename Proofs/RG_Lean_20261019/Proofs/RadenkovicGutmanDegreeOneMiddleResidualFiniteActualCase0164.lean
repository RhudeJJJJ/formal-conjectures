/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0164 : Family 8 := level8.get ⟨197,by decide⟩
def sourceMap0164 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0164 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0164_checked : acceptsGraphIso
    (source (graph core0164) (root 8) 2 2) DegreeOneMiddleResidualSpectrum348.graph sourceMap0164=true := by decide +kernel
theorem fusedMap0164_checked : acceptsGraphIso
    (fused (graph core0164) (root 8) 2 2) DegreeTwoThreeSpectrum2456.graph fusedMap0164=true := by decide +kernel
theorem certified0164 : Certified (graph core0164) (root 8) 2 2 :=
  of_native_maps core0164 DegreeOneMiddleResidualSpectrum348.graph DegreeTwoThreeSpectrum2456.graph
    sourceMap0164 fusedMap0164 sourceMap0164_checked fusedMap0164_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0164
#print axioms sourceMap0164_checked
#print axioms fusedMap0164_checked
#print axioms certified0164
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
