/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0328 : Family 9 := level9.get ⟨189,by decide⟩
def sourceMap0328 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,7,8,9,10,11,12] (sourceLabel 9 2 2 v)
def fusedMap0328 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0328_checked : acceptsGraphIso
    (source (graph core0328) (root 9) 2 2) DegreeOneMiddleResidualSpectrum814.graph sourceMap0328=true := by decide +kernel
theorem fusedMap0328_checked : acceptsGraphIso
    (fused (graph core0328) (root 9) 2 2) DegreeTwoThreeSpectrum3961.graph fusedMap0328=true := by decide +kernel
theorem certified0328 : Certified (graph core0328) (root 9) 2 2 :=
  of_native_maps core0328 DegreeOneMiddleResidualSpectrum814.graph DegreeTwoThreeSpectrum3961.graph
    sourceMap0328 fusedMap0328 sourceMap0328_checked fusedMap0328_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0328
#print axioms sourceMap0328_checked
#print axioms fusedMap0328_checked
#print axioms certified0328
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
