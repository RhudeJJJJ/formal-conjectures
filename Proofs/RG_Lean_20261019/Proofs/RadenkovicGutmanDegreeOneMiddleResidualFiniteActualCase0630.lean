/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0630 : Family 10 := level10.get ⟨199,by decide⟩
def sourceMap0630 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0630 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0630_checked : acceptsGraphIso
    (source (graph core0630) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1570.graph sourceMap0630=true := by decide +kernel
theorem fusedMap0630_checked : acceptsGraphIso
    (fused (graph core0630) (root 10) 2 2) DegreeTwoThreeSpectrum5180.graph fusedMap0630=true := by decide +kernel
theorem certified0630 : Certified (graph core0630) (root 10) 2 2 :=
  of_native_maps core0630 DegreeOneMiddleResidualSpectrum1570.graph DegreeTwoThreeSpectrum5180.graph
    sourceMap0630 fusedMap0630 sourceMap0630_checked fusedMap0630_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0630
#print axioms sourceMap0630_checked
#print axioms fusedMap0630_checked
#print axioms certified0630
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
