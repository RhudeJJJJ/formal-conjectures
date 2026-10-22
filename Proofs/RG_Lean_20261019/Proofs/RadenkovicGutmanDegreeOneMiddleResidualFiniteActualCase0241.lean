/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0241 : Family 9 := level9.get ⟨53,by decide⟩
def sourceMap0241 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap0241 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0241_checked : acceptsGraphIso
    (source (graph core0241) (root 9) 2 2) DegreeOneMiddleResidualSpectrum613.graph sourceMap0241=true := by decide +kernel
theorem fusedMap0241_checked : acceptsGraphIso
    (fused (graph core0241) (root 9) 2 2) DegreeTwoThreeSpectrum3938.graph fusedMap0241=true := by decide +kernel
theorem certified0241 : Certified (graph core0241) (root 9) 2 2 :=
  of_native_maps core0241 DegreeOneMiddleResidualSpectrum613.graph DegreeTwoThreeSpectrum3938.graph
    sourceMap0241 fusedMap0241 sourceMap0241_checked fusedMap0241_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0241
#print axioms sourceMap0241_checked
#print axioms fusedMap0241_checked
#print axioms certified0241
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
