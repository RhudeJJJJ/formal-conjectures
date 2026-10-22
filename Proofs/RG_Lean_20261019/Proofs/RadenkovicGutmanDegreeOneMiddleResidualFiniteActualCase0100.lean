/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0100 : Family 8 := level8.get ⟨55,by decide⟩
def sourceMap0100 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap0100 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0100_checked : acceptsGraphIso
    (source (graph core0100) (root 8) 2 2) DegreeOneMiddleResidualSpectrum306.graph sourceMap0100=true := by decide +kernel
theorem fusedMap0100_checked : acceptsGraphIso
    (fused (graph core0100) (root 8) 2 2) DegreeTwoThreeSpectrum2351.graph fusedMap0100=true := by decide +kernel
theorem certified0100 : Certified (graph core0100) (root 8) 2 2 :=
  of_native_maps core0100 DegreeOneMiddleResidualSpectrum306.graph DegreeTwoThreeSpectrum2351.graph
    sourceMap0100 fusedMap0100 sourceMap0100_checked fusedMap0100_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0100
#print axioms sourceMap0100_checked
#print axioms fusedMap0100_checked
#print axioms certified0100
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
