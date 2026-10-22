/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0551 : Family 10 := level10.get ⟨82,by decide⟩
def sourceMap0551 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0551 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0551_checked : acceptsGraphIso
    (source (graph core0551) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1701.graph sourceMap0551=true := by decide +kernel
theorem fusedMap0551_checked : acceptsGraphIso
    (fused (graph core0551) (root 10) 2 2) DegreeTwoThreeSpectrum4999.graph fusedMap0551=true := by decide +kernel
theorem certified0551 : Certified (graph core0551) (root 10) 2 2 :=
  of_native_maps core0551 DegreeOneMiddleResidualSpectrum1701.graph DegreeTwoThreeSpectrum4999.graph
    sourceMap0551 fusedMap0551 sourceMap0551_checked fusedMap0551_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0551
#print axioms sourceMap0551_checked
#print axioms fusedMap0551_checked
#print axioms certified0551
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
