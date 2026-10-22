/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0518 : Family 10 := level10.get ⟨39,by decide⟩
def sourceMap0518 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,16,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0518 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0518_checked : acceptsGraphIso
    (source (graph core0518) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1389.graph sourceMap0518=true := by decide +kernel
theorem fusedMap0518_checked : acceptsGraphIso
    (fused (graph core0518) (root 10) 2 2) DegreeTwoThreeSpectrum5111.graph fusedMap0518=true := by decide +kernel
theorem certified0518 : Certified (graph core0518) (root 10) 2 2 :=
  of_native_maps core0518 DegreeOneMiddleResidualSpectrum1389.graph DegreeTwoThreeSpectrum5111.graph
    sourceMap0518 fusedMap0518 sourceMap0518_checked fusedMap0518_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0518
#print axioms sourceMap0518_checked
#print axioms fusedMap0518_checked
#print axioms certified0518
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
