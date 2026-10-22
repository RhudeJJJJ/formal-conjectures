/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0248 : Family 9 := level9.get ⟨62,by decide⟩
def sourceMap0248 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap0248 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0248_checked : acceptsGraphIso
    (source (graph core0248) (root 9) 2 2) DegreeOneMiddleResidualSpectrum630.graph sourceMap0248=true := by decide +kernel
theorem fusedMap0248_checked : acceptsGraphIso
    (fused (graph core0248) (root 9) 2 2) DegreeTwoThreeSpectrum3968.graph fusedMap0248=true := by decide +kernel
theorem certified0248 : Certified (graph core0248) (root 9) 2 2 :=
  of_native_maps core0248 DegreeOneMiddleResidualSpectrum630.graph DegreeTwoThreeSpectrum3968.graph
    sourceMap0248 fusedMap0248 sourceMap0248_checked fusedMap0248_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0248
#print axioms sourceMap0248_checked
#print axioms fusedMap0248_checked
#print axioms certified0248
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
