/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0591 : Family 10 := level10.get ⟨136,by decide⟩
def sourceMap0591 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,16,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0591 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0591_checked : acceptsGraphIso
    (source (graph core0591) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1922.graph sourceMap0591=true := by decide +kernel
theorem fusedMap0591_checked : acceptsGraphIso
    (fused (graph core0591) (root 10) 2 2) DegreeTwoThreeSpectrum5067.graph fusedMap0591=true := by decide +kernel
theorem certified0591 : Certified (graph core0591) (root 10) 2 2 :=
  of_native_maps core0591 DegreeOneMiddleResidualSpectrum1922.graph DegreeTwoThreeSpectrum5067.graph
    sourceMap0591 fusedMap0591 sourceMap0591_checked fusedMap0591_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0591
#print axioms sourceMap0591_checked
#print axioms fusedMap0591_checked
#print axioms certified0591
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
