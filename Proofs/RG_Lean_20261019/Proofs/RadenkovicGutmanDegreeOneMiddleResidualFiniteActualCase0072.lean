/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0072 : Family 8 := level8.get ⟨15,by decide⟩
def sourceMap0072 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0072 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0072_checked : acceptsGraphIso
    (source (graph core0072) (root 8) 2 2) DegreeOneMiddleResidualSpectrum223.graph sourceMap0072=true := by decide +kernel
theorem fusedMap0072_checked : acceptsGraphIso
    (fused (graph core0072) (root 8) 2 2) DegreeTwoThreeSpectrum2359.graph fusedMap0072=true := by decide +kernel
theorem certified0072 : Certified (graph core0072) (root 8) 2 2 :=
  of_native_maps core0072 DegreeOneMiddleResidualSpectrum223.graph DegreeTwoThreeSpectrum2359.graph
    sourceMap0072 fusedMap0072 sourceMap0072_checked fusedMap0072_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0072
#print axioms sourceMap0072_checked
#print axioms fusedMap0072_checked
#print axioms certified0072
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
