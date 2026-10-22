/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0263 : Family 9 := level9.get ⟨84,by decide⟩
def sourceMap0263 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0263 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0263_checked : acceptsGraphIso
    (source (graph core0263) (root 9) 2 2) DegreeOneMiddleResidualSpectrum680.graph sourceMap0263=true := by decide +kernel
theorem fusedMap0263_checked : acceptsGraphIso
    (fused (graph core0263) (root 9) 2 2) DegreeTwoThreeSpectrum4040.graph fusedMap0263=true := by decide +kernel
theorem certified0263 : Certified (graph core0263) (root 9) 2 2 :=
  of_native_maps core0263 DegreeOneMiddleResidualSpectrum680.graph DegreeTwoThreeSpectrum4040.graph
    sourceMap0263 fusedMap0263 sourceMap0263_checked fusedMap0263_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0263
#print axioms sourceMap0263_checked
#print axioms fusedMap0263_checked
#print axioms certified0263
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
