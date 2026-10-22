/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0104 : Family 8 := level8.get ⟨61,by decide⟩
def sourceMap0104 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0104 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0104_checked : acceptsGraphIso
    (source (graph core0104) (root 8) 2 2) DegreeOneMiddleResidualSpectrum318.graph sourceMap0104=true := by decide +kernel
theorem fusedMap0104_checked : acceptsGraphIso
    (fused (graph core0104) (root 8) 2 2) DegreeTwoThreeSpectrum2360.graph fusedMap0104=true := by decide +kernel
theorem certified0104 : Certified (graph core0104) (root 8) 2 2 :=
  of_native_maps core0104 DegreeOneMiddleResidualSpectrum318.graph DegreeTwoThreeSpectrum2360.graph
    sourceMap0104 fusedMap0104 sourceMap0104_checked fusedMap0104_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0104
#print axioms sourceMap0104_checked
#print axioms fusedMap0104_checked
#print axioms certified0104
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
