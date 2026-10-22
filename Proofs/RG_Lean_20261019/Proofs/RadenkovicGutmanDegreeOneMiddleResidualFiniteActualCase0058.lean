/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0058 : Family 3 := level3.get ⟨1,by decide⟩
def sourceMap0058 : (Vertices 3 ⊕ Fin 5 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,11,12,13,1,2,3,4,5,6,7,8,9,10] (sourceLabel 3 4 4 v)
def fusedMap0058 : (Vertices 3 ⊕ Fin 10) → Fin 14 :=
  fun v => ![4,5,6,7,3,2,1,0,8,9,10,11,12,13] (fusedLabel 3 4 4 v)
theorem sourceMap0058_checked : acceptsGraphIso
    (source (graph core0058) (root 3) 4 4) DegreeOneMiddleResidualSpectrum056.graph sourceMap0058=true := by decide +kernel
theorem fusedMap0058_checked : acceptsGraphIso
    (fused (graph core0058) (root 3) 4 4) DegreeTwoThreeSpectrum1715.graph fusedMap0058=true := by decide +kernel
theorem certified0058 : Certified (graph core0058) (root 3) 4 4 :=
  of_native_maps core0058 DegreeOneMiddleResidualSpectrum056.graph DegreeTwoThreeSpectrum1715.graph
    sourceMap0058 fusedMap0058 sourceMap0058_checked fusedMap0058_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0058
#print axioms sourceMap0058_checked
#print axioms fusedMap0058_checked
#print axioms certified0058
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
