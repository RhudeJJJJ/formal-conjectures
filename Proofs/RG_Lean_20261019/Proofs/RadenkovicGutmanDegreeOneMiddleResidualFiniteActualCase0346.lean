/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0346 : Family 9 := level9.get ⟨222,by decide⟩
def sourceMap0346 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap0346 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0346_checked : acceptsGraphIso
    (source (graph core0346) (root 9) 2 2) DegreeOneMiddleResidualSpectrum850.graph sourceMap0346=true := by decide +kernel
theorem fusedMap0346_checked : acceptsGraphIso
    (fused (graph core0346) (root 9) 2 2) DegreeTwoThreeSpectrum4010.graph fusedMap0346=true := by decide +kernel
theorem certified0346 : Certified (graph core0346) (root 9) 2 2 :=
  of_native_maps core0346 DegreeOneMiddleResidualSpectrum850.graph DegreeTwoThreeSpectrum4010.graph
    sourceMap0346 fusedMap0346 sourceMap0346_checked fusedMap0346_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0346
#print axioms sourceMap0346_checked
#print axioms fusedMap0346_checked
#print axioms certified0346
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
