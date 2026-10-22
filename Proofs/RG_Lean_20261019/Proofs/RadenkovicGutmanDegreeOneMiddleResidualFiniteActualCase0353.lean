/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0353 : Family 9 := level9.get ⟨234,by decide⟩
def sourceMap0353 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap0353 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0353_checked : acceptsGraphIso
    (source (graph core0353) (root 9) 2 2) DegreeOneMiddleResidualSpectrum864.graph sourceMap0353=true := by decide +kernel
theorem fusedMap0353_checked : acceptsGraphIso
    (fused (graph core0353) (root 9) 2 2) DegreeTwoThreeSpectrum4027.graph fusedMap0353=true := by decide +kernel
theorem certified0353 : Certified (graph core0353) (root 9) 2 2 :=
  of_native_maps core0353 DegreeOneMiddleResidualSpectrum864.graph DegreeTwoThreeSpectrum4027.graph
    sourceMap0353 fusedMap0353 sourceMap0353_checked fusedMap0353_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0353
#print axioms sourceMap0353_checked
#print axioms fusedMap0353_checked
#print axioms certified0353
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
