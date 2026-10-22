/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0071 : Family 8 := level8.get ⟨14,by decide⟩
def sourceMap0071 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0071 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0071_checked : acceptsGraphIso
    (source (graph core0071) (root 8) 2 2) DegreeOneMiddleResidualSpectrum216.graph sourceMap0071=true := by decide +kernel
theorem fusedMap0071_checked : acceptsGraphIso
    (fused (graph core0071) (root 8) 2 2) DegreeTwoThreeSpectrum2354.graph fusedMap0071=true := by decide +kernel
theorem certified0071 : Certified (graph core0071) (root 8) 2 2 :=
  of_native_maps core0071 DegreeOneMiddleResidualSpectrum216.graph DegreeTwoThreeSpectrum2354.graph
    sourceMap0071 fusedMap0071 sourceMap0071_checked fusedMap0071_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0071
#print axioms sourceMap0071_checked
#print axioms fusedMap0071_checked
#print axioms certified0071
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
