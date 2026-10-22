/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0106 : Family 8 := level8.get ⟨63,by decide⟩
def sourceMap0106 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap0106 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0106_checked : acceptsGraphIso
    (source (graph core0106) (root 8) 2 2) DegreeOneMiddleResidualSpectrum321.graph sourceMap0106=true := by decide +kernel
theorem fusedMap0106_checked : acceptsGraphIso
    (fused (graph core0106) (root 8) 2 2) DegreeTwoThreeSpectrum2362.graph fusedMap0106=true := by decide +kernel
theorem certified0106 : Certified (graph core0106) (root 8) 2 2 :=
  of_native_maps core0106 DegreeOneMiddleResidualSpectrum321.graph DegreeTwoThreeSpectrum2362.graph
    sourceMap0106 fusedMap0106 sourceMap0106_checked fusedMap0106_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0106
#print axioms sourceMap0106_checked
#print axioms fusedMap0106_checked
#print axioms certified0106
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
